-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb38_original_finitecap_C1_slope_candidate_affine_reserve_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:22:45.134751+00:00
-- url     : https://prove2.me/submissions/156251e9-5a61-4542-916a-d9001630b156

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_global_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → y ≤ C.toReal →
      w 0 + y ≤ w y  := by
  have hSec :=
    avram_p3_bv_finite_cap_linear_global_secant
      C hC hFinite w hwCont hwSmooth hwGrad
  intro y hy0 hyC
  have h0C : (0 : ℝ) ≤ C.toReal := le_trans hy0 hyC
  have h := hSec 0 y (le_refl (0 : ℝ)) hy0
  dsimp only at h
  rw [if_pos hyC, if_pos h0C] at h
  linarith
