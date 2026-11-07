-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_centred_integrable_mean_gap_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:30:55.433704+00:00
-- url     : https://prove2.me/submissions/3581858b-488e-4af4-9151-6d60eeab0986

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
noncomputable section

/- An exact algebraic centring of the signed original excess. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F B : ℕ → Ω → ℝ) (k : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hBI : ∀ n, Integrable (B n) P)
    (hGap : Tendsto
      (fun n => max ((∫ ω, F n ω ∂P) - k -
        (∫ ω, B n ω ∂P)) 0)
      atTop (nhds (0 : ℝ))) :
    ∃ M : ℕ → Ω → ℝ,
      (∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable
        (fun ω => max (F n ω - (k + (M n ω + B n ω))) 0) P) ∧
      Tendsto
        (fun n => ∫ ω, max
          (F n ω - (k + (M n ω + B n ω))) 0 ∂P)
        atTop (nhds (0 : ℝ)) := by
  let m : ℕ → ℝ := fun n =>
    (∫ ω, F n ω ∂P) - (∫ ω, B n ω ∂P)
  let M : ℕ → Ω → ℝ := fun n ω => F n ω - B n ω - m n
  have hMInt (n : ℕ) : Integrable (M n) P :=
    ((hFI n).sub (hBI n)).sub (integrable_const (m n))
  have hMMean (n : ℕ) : (∫ ω, M n ω ∂P) = 0 := by
    have hSub : Integrable (fun ω => F n ω - B n ω) P :=
      (hFI n).sub (hBI n)
    change (∫ ω, (F n ω - B n ω) - m n ∂P) = 0
    rw [integral_sub hSub (integrable_const (m n))]
    rw [integral_sub (hFI n) (hBI n)]
    simp [m]
  have hErrEq (n : ℕ) (ω : Ω) :
      max (F n ω - (k + (M n ω + B n ω))) 0 =
        max ((∫ ω, F n ω ∂P) - k -
          (∫ ω, B n ω ∂P)) 0 := by
    dsimp only [M, m]
    congr 1
    ring
  refine ⟨M, ?_, ?_, ?_⟩
  · exact fun n => ⟨hMInt n, hMMean n⟩
  · intro n
    have heq :
        (fun ω => max (F n ω - (k + (M n ω + B n ω))) 0) =
          (fun _ : Ω => max ((∫ ω, F n ω ∂P) - k -
            (∫ ω, B n ω ∂P)) 0) := by
      funext ω
      exact hErrEq n ω
    rw [heq]
    exact integrable_const _
  · have heq :
        (fun n => ∫ ω, max (F n ω -
          (k + (M n ω + B n ω))) 0 ∂P) =
          (fun n => max ((∫ ω, F n ω ∂P) - k -
            (∫ ω, B n ω ∂P)) 0) := by
      funext n
      have hf :
          (fun ω => max (F n ω -
            (k + (M n ω + B n ω))) 0) =
            (fun _ : Ω => max ((∫ ω, F n ω ∂P) - k -
              (∫ ω, B n ω ∂P)) 0) := by
        funext ω
        exact hErrEq n ω
      rw [hf]
      simp
    rw [heq]
    exact hGap
