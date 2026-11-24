-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.one_le_mul_of_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:48.592805+00:00
-- url     : https://prove2.me/submissions/8d76749b-9f22-41f7-bf3c-73083b5f5bdf

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_norm_pow_sub_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
theorem _root_.solution {s : ℕ} {ζ : ℂ} (hs : 0 < s) (h : ζ ^ s = 1) (hne : ζ ≠ 1) :
    1 ≤ (s : ℝ) * ‖ζ - 1‖ := by
  have hn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h hs.ne'
  have hsum : ∑ i ∈ Finset.range s, ζ ^ i = 0 := by
    have := mul_geom_sum ζ s
    rw [h, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have h1 : ∑ i ∈ Finset.range s, (ζ ^ i - 1) = -(s : ℂ) := by
    rw [Finset.sum_sub_distrib, hsum]; simp
  have h2 : (s : ℝ) ≤ ∑ _i ∈ Finset.range s, (s : ℝ) * ‖ζ - 1‖ := by
    calc (s : ℝ) = ‖-(s : ℂ)‖ := by simp
      _ = ‖∑ i ∈ Finset.range s, (ζ ^ i - 1)‖ := by rw [h1]
      _ ≤ ∑ i ∈ Finset.range s, ‖ζ ^ i - 1‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun i hi => (norm_pow_sub_one_le hn i).trans
          (mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hi).le) (norm_nonneg _))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  exact le_of_mul_le_mul_left (by linarith) hs'
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
