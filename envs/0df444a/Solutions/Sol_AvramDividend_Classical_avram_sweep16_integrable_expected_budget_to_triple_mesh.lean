-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_integrable_expected_budget_to_triple_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:57:23.2432+00:00
-- url     : https://prove2.me/submissions/9fe1c063-bddf-4aa6-8aa8-59c35212dfb8

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
noncomputable section

/- Centring reduces an integrable original stopped reward budget to the exact triple-mesh witness shape. The substantive source obligation remains hBudget. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (K : ℝ)
    (hYInt : Integrable Y P)
    (hBudget : (∫ ω, Y ω ∂P) ≤ K) :
    ∃ Ymesh Mmesh Bmesh : ℕ → Ω → ℝ,
      ∃ M B DM DB : Ω → ℝ,
        (∀ n, AEStronglyMeasurable (Mmesh n) P) ∧
        (∀ n, AEStronglyMeasurable (Bmesh n) P) ∧
        Integrable DM P ∧ Integrable DB P ∧
        (∀ n, ∀ᵐ ω ∂P, |Mmesh n ω| ≤ DM ω) ∧
        (∀ n, ∀ᵐ ω ∂P, |Bmesh n ω| ≤ DB ω) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Ymesh n ω) atTop (nhds (Y ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω))) ∧
        (∀ᵐ ω ∂P, Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω))) ∧
        (∀ n, (∫ ω, Mmesh n ω ∂P) = 0) ∧
        (∀ n, (∫ ω, Bmesh n ω ∂P) ≤ 0) ∧
        (∀ᵐ ω ∂P, ∀ n, Ymesh n ω ≤ K + Mmesh n ω + Bmesh n ω) := by
  let μ : ℝ := ∫ ω, Y ω ∂P
  let m : Ω → ℝ := fun ω => Y ω - μ
  have hmInt : Integrable m P := hYInt.sub (integrable_const _)
  have hmMean : (∫ ω, m ω ∂P) = 0 := by
    have hEq : (∫ ω, Y ω - μ ∂P) = (∫ ω, Y ω ∂P) - μ := by
      rw [integral_sub hYInt (integrable_const _)]
      simp
    change (∫ ω, Y ω - μ ∂P) = 0
    rw [hEq]
    simp [μ]
  have hμ : μ ≤ K := hBudget
  refine ⟨(fun _ => Y), (fun _ => m), (fun _ _ => 0),
    m, (fun _ => 0), (fun ω => |m ω|), (fun _ => 0),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hmInt.aestronglyMeasurable
  · intro n
    exact (integrable_zero _ _ _ : Integrable (fun _ : Ω => (0 : ℝ)) P).aestronglyMeasurable
  · exact hmInt.abs
  · exact integrable_zero _ _ _
  · intro n
    filter_upwards [] with ω
    exact le_rfl
  · intro n
    filter_upwards [] with ω
    norm_num
  · filter_upwards [] with ω
    exact tendsto_const_nhds
  · filter_upwards [] with ω
    exact tendsto_const_nhds
  · filter_upwards [] with ω
    exact tendsto_const_nhds
  · intro n
    exact hmMean
  · intro n
    simp
  · filter_upwards [] with ω
    intro n
    change Y ω ≤ K + (Y ω - μ) + 0
    linarith
