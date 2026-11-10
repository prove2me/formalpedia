-- Prove2me | solution 1 for AvramDividend.Classical.avram_gtop24_bounded_withtop_stop_has_nnreal_rep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T03:13:03.377869+00:00
-- url     : https://prove2.me/submissions/6f946fb7-30ab-43b5-ad9b-51d0f9e48c49

import Mathlib.Probability.Process.Stopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (σ : Ω → ℝ≥0)
    (R : Ω → WithTop ℝ≥0)
    (hRstop : IsStoppingTime 𝓕.rightCont R)
    (hRle : ∀ ω, R ω ≤ (σ ω : WithTop ℝ≥0)) :
    ∃ L : Ω → ℝ≥0,
      (∀ ω, (L ω : WithTop ℝ≥0) = R ω) ∧
      IsStoppingTime 𝓕.rightCont (fun ω => (L ω : WithTop ℝ≥0)) ∧
      ∀ ω, L ω ≤ σ ω := by
  classical
  let L : Ω → ℝ≥0 := fun ω => (R ω).getD 0
  have hEq : ∀ ω, (L ω : WithTop ℝ≥0) = R ω := by
    intro ω
    cases h : R ω with
    | top =>
        have hle : (⊤ : WithTop ℝ≥0) ≤ (σ ω : WithTop ℝ≥0) := by
          simpa only [h] using hRle ω
        exact False.elim ((not_le_of_gt (WithTop.coe_lt_top (σ ω))) hle)
    | coe a =>
        change (((R ω).getD (0 : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) =
          (a : WithTop ℝ≥0)
        rw [h]
        rfl
  refine ⟨L, hEq, ?_, ?_⟩
  · convert hRstop using 1
    funext ω
    exact hEq ω
  · intro ω
    exact WithTop.coe_le_coe.mp ((hEq ω).le.trans (hRle ω))
