-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.restrictedLattice_divStable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:43.248719+00:00
-- url     : https://prove2.me/submissions/76ab673e-f842-4e99-b5ee-af436d7206e8

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_restrictedLattice_divided_power
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_dW_pow_y
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_uop_pow_y
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_pow_y
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
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_setLast
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_glAct
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_pderiv
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_restriction_raising_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_divided_integral_holds
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
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K : ℕ}
variable {s : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hU : UDivInt) (hD : DWDivInt) (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k)
    (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1)) (hE : G.E = EX p LL c) :
    DivStable G.E (M2 p LL J M (Fin.last s)).toAddSubgroup := by
  rw [hE]
  intro a b hab k x hx
  rw [Submodule.mem_toAddSubgroup] at hx ⊢
  cases a using Fin.cases with
  | zero =>
    cases b using Fin.cases with
    | zero => exact absurd rfl hab
    | succ j =>
      simp only [EX, Fin.cases_zero, Fin.cases_succ]
      have hne : ((Fin.last K, Fin.castSucc j) : Fin (K + 1) × Fin (s + 1)) ≠ (Fin.last K, Fin.last s) :=
        fun h => (Fin.castSucc_lt_last j).ne (congrArg Prod.snd h)
      refine restrictedLattice_divided_power LL J M (Fin.last s) (dW p K (Fin.castSucc j)) (dW p K (Fin.castSucc j)) k ?_ ?_ ?_ x hx
      · intro y
        exact resL_pderiv _ _ hne 0 y
      · intro y hy
        exact hD p K (s + 1) (Fin.castSucc j) k y hy
      · intro o h hh
        exact ⟨o - k, dW_pow_y LL hv J M (Fin.castSucc j) o k h hh⟩
  | succ i =>
    cases b using Fin.cases with
    | zero =>
      simp only [EX, Fin.cases_zero, Fin.cases_succ]
      refine restrictedLattice_divided_power LL J M (Fin.last s) (Uop p LL c univ (Fin.castSucc i))
        (Uop p LL c (univ.erase (Fin.last s)) (Fin.castSucc i)) k ?_ ?_ ?_ x hx
      · intro y
        rw [resL_apply, resL_apply]
        exact restriction_raising_holds p K (s + 1) LL c (Fin.last s) (Fin.castSucc i) y (Fin.castSucc_lt_last i).ne
      · intro y hy
        exact hU p K (s + 1) LL c univ (Fin.castSucc i) k (Finset.mem_univ _) y hy
      · intro o h hh
        exact ⟨o + k, uop_pow_y LL hv J M c k0 hk0 hc hmin (Fin.castSucc i) o k h hh⟩
    | succ j =>
      have hij : i ≠ j := fun h => hab (h ▸ rfl)
      simp only [EX, Fin.cases_succ]
      refine restrictedLattice_divided_power LL J M (Fin.last s) (glAct p LL (K + 1) (Fin.castSucc i) (Fin.castSucc j))
        (glAct p LL (K + 1) (Fin.castSucc i) (Fin.castSucc j)) k ?_ ?_ ?_ x hx
      · intro y
        refine resL_glAct LL (K + 1) _ _ _ 0 (fun l _ => ⟨?_, ?_⟩) y
        · exact fun h => (Fin.castSucc_lt_last i).ne (congrArg Prod.snd h)
        · exact fun h => (Fin.castSucc_lt_last j).ne (congrArg Prod.snd h)
      · intro y hy
        exact divided_integral_holds p (K + 1) (s + 1) LL (K + 1) (Fin.castSucc i) (Fin.castSucc j)
          (fun h => hij (Fin.castSucc_injective _ h)) k y hy
      · intro o h hh
        have h1 := glAct_pow_y (setLast LL o) J M (Fin.castSucc i) (Fin.castSucc j) k h hh
        rw [glAct_setLast] at h1
        exact ⟨o, h1⟩
end Formalism.InvariantFactorPaths.L4
