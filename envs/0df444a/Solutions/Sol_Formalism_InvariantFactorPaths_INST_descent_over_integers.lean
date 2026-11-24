-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.descent_over_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:58:09.221179+00:00
-- url     : https://prove2.me/submissions/91499054-6bc9-4134-9840-e0978ccdba8f

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Descent
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_dsc_denominator
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_dsc_split
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_dsc_approx
import Theorems.Thm_Formalism_InvariantFactorPaths_INST_dsc_divide
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
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylSat
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual
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
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution : DescentZ := by
  intro p _ r n hn ν hν e hyp f hf
  obtain ⟨N, hN0, hN⟩ := dsc_denominator r n hn ν hν
  obtain ⟨k, c, hNc, hc⟩ := dsc_split p N hN0
  have hmf : map (Int.castRingHom ℤ_[p]) f ∈ dualWeyl ℤ_[p] r n ν :=
    dualWeylMap ℤ ℤ_[p] (Int.castRingHom ℤ_[p]) r n ν f hf
  obtain ⟨d, hd, z, hz⟩ := dsc_approx p r n hn ν k _ (hyp _ hmf)
  have hmap : map (Int.castRingHom ℤ_[p]) (((p : ℤ) ^ e) • f - d) = ((p : ℤ_[p]) ^ k) • z := by
    rw [map_sub, smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    have : (Int.castRingHom ℤ_[p]) ((p : ℤ) ^ e) = (p : ℤ_[p]) ^ e := by simp
    rw [this, hz]; abel
  obtain ⟨g1, hg1⟩ := dsc_divide p k _ z hmap
  have hg0 : ((p : ℤ) ^ e) • f - d ∈ dualWeyl ℤ r n ν :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hf) (weylLeDual ℤ r n hn ν hν hd)
  have hpk : ((p : ℤ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hg1m : g1 ∈ dualWeyl ℤ r n ν := dualWeylSat ℤ r n ν _ g1 hpk (hg1 ▸ hg0)
  refine ⟨c, hc, ?_⟩
  have key : (c * (p : ℤ) ^ e) • f = c • d + N • g1 := by
    rw [hNc, mul_comm ((p : ℤ) ^ k) c, mul_smul, mul_smul, ← hg1, smul_sub]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hd) (hN g1 hg1m)
end Formalism.InvariantFactorPaths.INST
