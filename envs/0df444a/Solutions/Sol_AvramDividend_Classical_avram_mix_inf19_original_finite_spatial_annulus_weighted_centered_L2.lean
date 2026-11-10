-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf19_original_finite_spatial_annulus_weighted_centered_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:37:21.706099+00:00
-- url     : https://prove2.me/submissions/a81cac43-cb42-4089-a234-bbcdc6ab9bc2

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Every finite deterministic spatial weighting of the intrinsic compensated
negative-annulus counts is square integrable and centred on the actual path space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (cut : ℕ → ℕ) (hcut : Monotone cut) (a : ℕ → ℝ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
    ∀ k : ℕ,
      MemLp (fun ω => ∑ i ∈ Finset.range k, a i * Y i ω) 2 P ∧
      (∫ ω, ∑ i ∈ Finset.range k, a i * Y i ω ∂P) = 0 := by
  classical
  let B : ℕ → Set ℝ := fun i =>
    Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B i)
  let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
  let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
  change ∀ k : ℕ,
    MemLp (fun ω => ∑ i ∈ Finset.range k, a i * Y i ω) 2 P ∧
    (∫ ω, ∑ i ∈ Finset.range k, a i * Y i ω ∂P) = 0
  intro k
  let grid : ℕ → ℝ≥0 := fun j => if j = 0 then 0 else T
  have hGrid : ∀ j, grid j ≤ grid (j + 1) := by
    intro j
    by_cases hj : j = 0
    · subst j
      simp [grid]
    · simp [grid, hj, Nat.succ_ne_zero]
  have hH : ∀ j, StronglyMeasurable[𝓕.rightCont (grid j)]
      (fun _ : Ω => (1 : ℝ)) := by
    intro j
    exact stronglyMeasurable_const
  have hBound : ∀ (j : ℕ) (ω : Ω), |(1 : ℝ)| ≤ (1 : ℝ) := by
    intro j ω
    norm_num
  have hY (i : ℕ) : MemLp (Y i) 2 P ∧ (∫ ω, Y i ω ∂P) = 0 := by
    have hOne :=
      avram_mix_annulus15_original_bounded_predictable_annulus_grid_L2_zero_mean
        X (cut i) (cut (i + 1)) (hcut (Nat.le_succ i))
        grid hGrid (fun _ (_ : Ω) => (1 : ℝ)) hH (1 : ℝ) hBound 1
    simpa [grid, B, N, r, Y] using hOne
  have hFinite (s : Finset ℕ) :
      MemLp (fun ω => ∑ i ∈ s, a i * Y i ω) 2 P ∧
      (∫ ω, ∑ i ∈ s, a i * Y i ω ∂P) = 0 := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        constructor
        · simpa using (memLp_zero : MemLp (fun _ : Ω => (0 : ℝ)) 2 P)
        · simp
    | @insert i s his hs =>
        have hi : MemLp (fun ω => a i * Y i ω) 2 P := (hY i).1.const_mul (a i)
        have hintegrable : Integrable (fun ω => a i * Y i ω) P :=
          hi.integrable (by norm_num)
        have hsintegrable : Integrable (fun ω => ∑ j ∈ s, a j * Y j ω) P :=
          hs.1.integrable (by norm_num)
        constructor
        · have hEq :
              (fun ω => ∑ j ∈ insert i s, a j * Y j ω) =
                (fun ω => a i * Y i ω) +
                  (fun ω => ∑ j ∈ s, a j * Y j ω) := by
            funext ω
            simp [Finset.sum_insert his, Pi.add_apply]
          rw [hEq]
          exact hi.add hs.1
        · have heq := integral_add hintegrable hsintegrable
          simpa [Finset.sum_insert his, integral_const_mul, (hY i).2, hs.2] using heq
  exact hFinite (Finset.range k)
