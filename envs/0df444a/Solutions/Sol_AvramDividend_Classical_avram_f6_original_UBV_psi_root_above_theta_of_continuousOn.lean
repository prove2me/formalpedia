-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_UBV_psi_root_above_theta_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:32:34.853743+00:00
-- url     : https://prove2.me/submissions/c02eceac-b6fc-4866-86a1-dcc13f5d11dd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (θ : ℝ)
    (hψCont : ContinuousOn X.ψ (Icc (0 : ℝ) (max θ 0))) :
    ∃ p lam : ℝ, 0 < p ∧ 0 < lam ∧ θ < lam ∧ X.ψ lam = p := by
  have hK : IsCompact (X.ψ '' Icc (0 : ℝ) (max θ 0)) :=
    isCompact_Icc.image_of_continuousOn hψCont
  obtain ⟨M, hM⟩ := hK.bddAbove
  let q : ℝ := max M 0 + 1
  have hq : 0 < q := by
    dsimp [q]
    have h := le_max_right M 0
    linarith
  obtain ⟨lam, hlam, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hBV q hq
  have hθ : θ < lam := by
    by_contra hn
    have hle : lam ≤ θ := le_of_not_gt hn
    have hmem : lam ∈ Icc (0 : ℝ) (max θ 0) :=
      ⟨hlam.le, le_trans hle (le_max_left θ 0)⟩
    have hb : X.ψ lam ≤ M := hM ⟨lam, hmem, rfl⟩
    rw [hroot] at hb
    have hh := le_max_left M 0
    dsimp [q] at hb
    linarith
  exact ⟨q, lam, hq, hlam, hθ, hroot⟩
