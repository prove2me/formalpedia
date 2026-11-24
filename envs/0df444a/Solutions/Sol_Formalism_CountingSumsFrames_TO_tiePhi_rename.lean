-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.tiePhi_rename
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:49.819815+00:00
-- url     : https://prove2.me/submissions/879f66c7-f0c2-4b54-96c3-ae09fa13a7fa

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_tieE_rename
import Theorems.Thm_Formalism_CountingSumsFrames_TO_tieF_rename
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {τ : Type} {r : ℕ} (ι : σ → τ) (hι : Function.Injective ι) (w e : Fin r → σ) (o n z : ℕ)
    (F : MvPolynomial σ k) :
    Formalism.GM.tiePhi (fun c => ι (w c)) (fun c => ι (e c)) o n z (rename ι F) =
      rename ι (Formalism.GM.tiePhi w e o n z F) := by
  have hE : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieE (fun c => ι (w c)) (fun c => ι (e c))) ^ j) (rename ι G) =
        rename ι (((Formalism.GM.tieE w e) ^ j) G) := by
    intro j
    induction j with
    | zero => intro G; simp
    | succ j ih => intro G; rw [pow_succ, Module.End.mul_apply, tieE_rename, ih, pow_succ, Module.End.mul_apply]
  have hF : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieF (fun c => ι (w c)) (fun c => ι (e c))) ^ j) (rename ι G) =
        rename ι (((Formalism.GM.tieF w e) ^ j) G) := by
    intro j
    induction j with
    | zero => intro G; simp
    | succ j ih => intro G; rw [pow_succ, Module.End.mul_apply, tieF_rename ι hι, ih, pow_succ, Module.End.mul_apply]
  simp only [Formalism.GM.tiePhi, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, hF, hE]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← AlgHom.toLinearMap_apply (rename ι), map_smul]
  rfl
end Formalism.CountingSumsFrames.TO
