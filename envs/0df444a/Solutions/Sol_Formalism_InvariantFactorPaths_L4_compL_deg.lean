-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.compL_deg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:37.629096+00:00
-- url     : https://prove2.me/submissions/5af16b14-b18d-4dfc-a73d-582aeeb4a9d0

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP
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
variable {r : ℕ} [NeZero r]
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (o o' : ℕ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hx : x ∈ Pol p r (setLast LL o')) :
    compL ℚ_[p] (fun m : Fin (K + 1) × Fin r →₀ ℕ => ∑ a, m (Fin.last K, a) = o) x = if o' = o then x else 0 := by
  ext m
  change MvPolynomial.coeff m (compP _ x) = _
  rw [coeff_compP]
  by_cases hm : m ∈ x.support
  · have hmd : MultiDeg (setLast LL o') m := ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hx) hm
    have hs : ∑ a, m (Fin.last K, a) = o' := by
      rw [hmd (Fin.last K)]
      simp [setLast]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hs.symm.trans h1) h2
    · exact absurd (hs.trans h2) h1
    · simp
  · have h0 : MvPolynomial.coeff m x = 0 := by
      by_contra hne
      exact hm (MvPolynomial.mem_support_iff.2 hne)
    split_ifs <;> simp [h0]
end Formalism.InvariantFactorPaths.L4
