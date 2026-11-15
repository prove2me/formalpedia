-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb40_original_finitecap_C1_preruin_candidate_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:25:15.886517+00:00
-- url     : https://prove2.me/submissions/0520746e-62d4-4da8-9fd5-4e4533d14148

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_global_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)  := by
  have hSec :=
    avram_p3_bv_finite_cap_linear_global_secant
      C hC hFinite w hwCont hwSmooth hwGrad
  intro ω t _ ht
  obtain ⟨hU0, hUC⟩ :=
    capped_riskProcess_range_before_ruin_including_zero
      X x hx C hxc D hD ω t ht
  have hUCap : riskProcess X x D t ω ≤ C.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hFinite).mp hUC
  have h0C : (0 : ℝ) ≤ C.toReal := le_trans hU0 hUCap
  have h := hSec 0 (riskProcess X x D t ω)
    (le_refl (0 : ℝ)) hU0
  dsimp only at h
  rw [if_pos hUCap, if_pos h0C] at h
  linarith
