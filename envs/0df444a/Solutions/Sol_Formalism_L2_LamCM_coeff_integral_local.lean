-- Prove2me | solution 1 for Formalism.L2.LamCM.coeff_integral_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:21:33.085828+00:00
-- url     : https://prove2.me/submissions/eaf96fed-5f03-405b-8a38-ea66dc8c61f3

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementS
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_LargeResidueExtensionLemma
import Theorems.Thm_Formalism_L2_LamCM_evalFr_substFr
import Theorems.Thm_Formalism_L2_LamCM_substFr_C_mul
import Theorems.Thm_Formalism_L2_LamCM_map_substFr
import Theorems.Thm_Formalism_L2_LamCM_evalFr_C_mul
import Theorems.Thm_Formalism_L2_LamCM_subst_eval
import Theorems.Thm_Formalism_L2_LamCM_large_residue_extension_lemma
import Theorems.Thm_Formalism_L2_LamCM_substGauss


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing
namespace Formalism.L2.LamCM
theorem _root_.solution : CoeffIntegralLoc := by
  intro V K' _ _ _ _ _ _ B _ m G U c τ hV hfin hτ hU hc hG μ
  classical
  have hUu : ∀ b, IsUnit (U b).det := fun b => isUnit_iff_ne_zero.mpr (hU b)
  set P : MvPolynomial (FrVar m) K' := C τ⁻¹ * substFr (fun b => (U b)⁻¹) G with hP
  have hPc : ∀ ν, coeff ν P ∈ Set.range (algebraMap V K') := by
    refine large_residue_extension_lemma V K' B m P hV hfin ?_
    intro W KW _ _ _ _ _ _ _ f hW hWf hloc hcomp X hX
    obtain ⟨w, hw⟩ := hG W KW f hW hWf hloc hcomp
      (fun b => (((U b)⁻¹).map f).transpose * (X b).map (algebraMap W KW)) X hX (by
        intro b
        rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (hUu b),
          Matrix.map_one _ (map_zero f) (map_one f), Matrix.transpose_one, Matrix.one_mul])
    refine ⟨w, ?_⟩
    rw [hP, map_mul, map_C, map_substFr, evalFr_C_mul, evalFr_substFr]
    rw [hw, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hτ, map_one, one_mul]
  have hS := substGauss V K' B m P U c hPc hc μ
  have hsub : substFr U P = C τ⁻¹ * G := by
    rw [hP, substFr_C_mul, (subst_eval K' B m G U).2.1 hUu]
  obtain ⟨w, hw⟩ := hS
  refine ⟨w, ?_⟩
  rw [hsub, coeff_C_mul] at hw
  rw [hw]
  field_simp
end Formalism.L2.LamCM
