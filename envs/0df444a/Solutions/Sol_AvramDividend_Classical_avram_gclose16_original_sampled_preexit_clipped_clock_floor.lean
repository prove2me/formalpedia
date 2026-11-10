-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose16_original_sampled_preexit_clipped_clock_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T21:30:24.363825+00:00
-- url     : https://prove2.me/submissions/1204d0b1-fa0e-45dc-be70-3cd23874e043

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_sampled_lower_exit_stopping
import Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_dense_lower_preexit_floor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Clip an original stopping clock at the first dense sampled lower exit.
The clipped clock is stopped and all earlier reserve values retain the floor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → WithTop ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont σ)
    (r : ℕ → ℝ≥0)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U)
    (δ : ℝ) :
    let E : Ω → WithTop ℝ≥0 := fun ω =>
      ⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ
        then (r k : WithTop ℝ≥0) else ⊤
    let ρ : Ω → WithTop ℝ≥0 := fun ω => min (σ ω) (E ω)
    IsStoppingTime 𝓕.rightCont ρ ∧
      (∀ ω, ρ ω ≤ σ ω) ∧
      ∀ (ω : Ω) (T : ℝ≥0), (T : WithTop ℝ≥0) ≤ ρ ω →
        ∀ s : ℝ≥0, s < T →
          δ ≤ x + X.X s ω - rightLimit D s ω := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · exact hσstop.min
      (avram_gfinite15_original_sampled_lower_exit_stopping X x D hD r δ)
  · intro ω
    exact min_le_left _ _
  · intro ω T hT s hs
    have hTE : (T : WithTop ℝ≥0) ≤
        (⨅ k : ℕ, if x + X.X (r k) ω - rightLimit D (r k) ω < δ
          then (r k : WithTop ℝ≥0) else ⊤) :=
      le_trans hT (min_le_right _ _)
    exact (avram_gfinite15_original_dense_lower_preexit_floor
      X x D hD r δ hgrid ω T hTE) s hs
