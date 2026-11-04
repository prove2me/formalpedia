-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_expected_budget_witness_of_original_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:46:44.864762+00:00
-- url     : https://prove2.me/submissions/20fd85d4-75ab-44df-bbb6-11642c0713c7

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An integrable original-source expected stopped dividend budget can be
    centred into the exact integrable signed-residual witness on X's own law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (x : ℝ)
    (Term Cash : Ω → ℝ)
    (hTermI : Integrable Term P) (hCashI : Integrable Cash P)
    (hBudget : (∫ ω, Term ω + Cash ω ∂P) ≤ w x) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let S : Ω → ℝ := fun ω => Term ω + Cash ω
  let e : ℝ := ∫ ω, S ω ∂P
  let M : Ω → ℝ := fun ω => S ω - e
  let G : Ω → ℝ := fun _ => e - w x
  let H : Ω → ℝ := fun _ => 0
  have hS : Integrable S P := hTermI.add hCashI
  have hM : Integrable M P := hS.sub (integrable_const e)
  have hMean : e ≤ w x := by
    change (∫ ω, Term ω + Cash ω ∂P) ≤ w x
    exact hBudget
  refine ⟨M, G, H, hM, integrable_const _, integrable_const _, ?_, ?_, ?_⟩
  · change (∫ ω, S ω - e ∂P) = 0
    rw [integral_sub hS (integrable_const e)]
    simp [e]
  · filter_upwards [] with ω
    change e - w x + 0 ≤ 0
    linarith
  · filter_upwards [] with ω
    change S ω ≤ w x + (S ω - e) + (e - w x) + 0
    linarith