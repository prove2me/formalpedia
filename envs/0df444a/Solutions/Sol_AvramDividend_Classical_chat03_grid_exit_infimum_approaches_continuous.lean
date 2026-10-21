-- Prove2me | solution 1 for AvramDividend.Classical.chat03_grid_exit_infimum_approaches_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T21:36:13.73435+00:00
-- url     : https://prove2.me/submissions/4cb06012-c245-4d6e-aa91-a62e6c4763d8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_exit_mesh_approximation
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
The infimum σ of genuine strict exits sampled on a sufficiently fine
uniform grid approaches the true continuous strict-exit infimum τ from
above. No attainment of τ or right-continuous filtration is assumed.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
      ∀ σ : ℝ≥0,
        IsGLB
          {s : ℝ≥0 | ∃ k : ℕ,
            s = (k : ℝ≥0) * h ∧
            (X.X s ω < lower ∨ upper < X.X s ω)} σ →
        τ ≤ σ ∧ σ < τ + ε := by
  obtain ⟨δ, hδ, hmesh⟩ :=
    chat03_strict_exit_mesh_approximation X ω lower upper τ hτ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhd σ hσ
  obtain ⟨k, hτk, hkε, hkExit⟩ := hmesh h hh hhd
  have hτlb : τ ∈ lowerBounds
      {s : ℝ≥0 | ∃ j : ℕ,
        s = (j : ℝ≥0) * h ∧
        (X.X s ω < lower ∨ upper < X.X s ω)} := by
    intro s hs
    rcases hs with ⟨j, hj, hsj⟩
    exact hτ.1 hsj
  have hleft : τ ≤ σ := hσ.2 hτlb
  have hright :
      σ ≤ (k : ℝ≥0) * h := by
    exact hσ.1 ⟨k, rfl, hkExit⟩
  exact ⟨hleft, hright.trans_lt hkε⟩