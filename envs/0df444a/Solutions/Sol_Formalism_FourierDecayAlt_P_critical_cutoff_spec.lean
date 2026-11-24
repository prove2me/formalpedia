-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.critical_cutoff_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:51.273303+00:00
-- url     : https://prove2.me/submissions/6fb3ee49-16b4-44ba-8631-78baccaa5cdc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_smooth_cutoff_eq_zero_of_two_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_common_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_critCut_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_critCut_le_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_critCut_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_lt_of_critCut_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_critCut_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_critCut_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_critCut_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_exists_norm_iteratedFDeriv_critCut_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_root_sep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G6 Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.CritCutSpec := by
  intro m δ hδ
  refine ⟨fun z x => ⟨critCut_nonneg δ z x, critCut_le_one δ z x, critCut_eq_one hδ, critCut_eq_zero hδ⟩,
    fun k => ?_, ?_⟩
  · obtain ⟨C, _, hC⟩ := common_bound k
      (fun j (x : Fin (m + 1) → ℂ) => ‖iteratedFDeriv ℝ j (critCut δ 0) x‖) (exists_norm_iteratedFDeriv_critCut_le (m + 1) hδ)
    refine ⟨C, fun z => ⟨critCut_contDiff δ z (n := k), fun j hj x => ?_⟩⟩
    rw [critCut_shift δ z, iteratedFDeriv_comp_sub]
    exact hC j hj _
  · intro z z' x hzz hne hz hx
    have h1 : ‖x 0 - z‖ < 2 * δ := lt_of_critCut_ne_zero hδ hx 0
    have h2 : ‖z‖ ≤ ((m + 2 : ℕ) : ℝ) * ‖z - z'‖ := root_sep (by omega) hzz hne
    push_cast at h2
    have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have h3 : 100 * δ ≤ ‖z - z'‖ := by
      have : ((m : ℝ) + 2) * (100 * δ) ≤ ((m : ℝ) + 2) * ‖z - z'‖ := by linarith
      exact le_of_mul_le_mul_left this hm
    have h4 : ‖z - z'‖ ≤ ‖x 0 - z‖ + ‖x 0 - z'‖ := by
      have e : z - z' = -(x 0 - z) + (x 0 - z') := by ring
      rw [e]
      exact (norm_add_le _ _).trans (by rw [norm_neg])
    have h5 : 2 * δ ≤ ‖x 0 - z'‖ := by linarith
    refine Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (m + 1))) (smooth_cutoff_eq_zero_of_two_le ?_)
    rw [le_div_iff₀ (by positivity)]
    nlinarith
end Formalism.FourierDecayAlt.P
