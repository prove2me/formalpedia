-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.all_first_level_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:36:42.542961+00:00
-- url     : https://prove2.me/submissions/662c74df-6d5d-4c66-9689-947eaaf47976

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductFactorBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_ProductFactorBounds_prod_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_ProductFactorBounds_factor_bounds_first

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.ProductFactorBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.AllFirstBounds := by
  intro N w Y hN hlen h hfirst
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < (N : ℝ) ^ 2 - 1 := by linarith
  have hpos2 : (0 : ℝ) < ((N : ℝ) ^ 2 - 1) ^ 2 := by positivity
  have hlenr : (w.length : ℝ) ≤ N := by exact_mod_cast hlen
  have a0 : 0 ≤ 1 / ((N : ℝ) ^ 2 - 1) ^ 2 := (one_div_pos.2 hpos2).le
  have a1 : 1 / ((N : ℝ) ^ 2 - 1) ^ 2 ≤ 1 := by
    rw [div_le_one hpos2]; nlinarith
  obtain ⟨lo, hi⟩ := prod_bounds (1 / ((N : ℝ) ^ 2 - 1) ^ 2) 0 a1 le_rfl
    (w.map fun l => wFactor l Y) (by
      intro f hf
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hf
      exact factor_bounds_first N hNr l Y (h l hl) (hfirst l hl))
  rw [List.length_map] at lo hi
  constructor
  · refine le_trans ?_ lo
    have hb := one_add_mul_le_pow (a := -(1 / ((N : ℝ) ^ 2 - 1) ^ 2)) (by linarith) w.length
    have e : (1 : ℝ) + -(1 / ((N : ℝ) ^ 2 - 1) ^ 2) = 1 - 1 / ((N : ℝ) ^ 2 - 1) ^ 2 := by ring
    rw [e] at hb
    refine le_trans ?_ hb
    have h1 : (w.length : ℝ) * (1 / ((N : ℝ) ^ 2 - 1) ^ 2) ≤ N * (1 / ((N : ℝ) ^ 2 - 1) ^ 2) :=
      mul_le_mul_of_nonneg_right hlenr a0
    have h2 : (N : ℝ) * (1 / ((N : ℝ) ^ 2 - 1) ^ 2) ≤ 2 / (N : ℝ) ^ 3 := by
      rw [mul_one_div, div_le_div_iff₀ hpos2 (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.2 hN2) (sub_nonneg.2 hN2)]
    linarith
  · simpa using hi
end Formalism.FourierDecayAlt.P
