-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.restrictedLattice_divided_power
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:38.68601+00:00
-- url     : https://prove2.me/submissions/ba46bdfa-0f61-4525-8b9a-19b5ef070dd2

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_restrictedLattice_of_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_restrictedLattice_map_le
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pow_intertwine
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
theorem _root_.solution (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (A B : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (k : ℕ)
    (hAB : ∀ x, resL p (Fin.last K, ρ) 0 (A x) = B (resL p (Fin.last K, ρ) 0 x))
    (hint : ∀ x ∈ IntPol p (Fin (K + 1) × Fin r),
      ((k.factorial : ℚ_[p]))⁻¹ • (A ^ k) x ∈ IntPol p (Fin (K + 1) × Fin r))
    (hY : ∀ o : ℕ, ∀ h ∈ Y p (setLast LL o) J M, ∃ o' : ℕ, (A ^ k) h ∈ Y p (setLast LL o') J M) :
    ∀ z ∈ M2 p LL J M ρ, ((k.factorial : ℚ_[p]))⁻¹ • (B ^ k) z ∈ M2 p LL J M ρ := by
  intro z hz
  have key : ∀ o : ℕ, ∀ h ∈ Y p (setLast LL o) J M, h ∈ IntPol p (Fin (K + 1) × Fin r) →
      (((k.factorial : ℚ_[p]))⁻¹ • (B ^ k)) (initPart (Fin.last K, ρ) 0 h) ∈ M2 p LL J M ρ := by
    intro o h hh hi
    obtain ⟨o', ho'⟩ := hY o h hh
    have e1 : (B ^ k) (initPart (Fin.last K, ρ) 0 h) = initPart (Fin.last K, ρ) 0 ((A ^ k) h) :=
      (pow_intertwine (resL p (Fin.last K, ρ) 0) A B hAB k h).symm
    have e2 : initPart (Fin.last K, ρ) 0 (((k.factorial : ℚ_[p]))⁻¹ • (A ^ k) h)
        = ((k.factorial : ℚ_[p]))⁻¹ • initPart (Fin.last K, ρ) 0 ((A ^ k) h) :=
      (resL p (Fin.last K, ρ) 0).map_smul _ _
    rw [LinearMap.smul_apply, e1, ← e2]
    exact mem_restrictedLattice_of_mem LL J M ρ o' _ (Submodule.smul_mem _ _ ho') (hint h hi)
  have := restrictedLattice_map_le LL J M ρ (((k.factorial : ℚ_[p]))⁻¹ • (B ^ k)) key z hz
  simpa only [LinearMap.smul_apply] using this
end Formalism.InvariantFactorPaths.L4
