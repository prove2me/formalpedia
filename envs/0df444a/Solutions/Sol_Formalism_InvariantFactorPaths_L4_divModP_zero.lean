-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.divModP_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:28:48.027629+00:00
-- url     : https://prove2.me/submissions/5128b290-38c7-45de-a264-e6b03a55314f

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundUnconditionalOfSat
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
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_initPart_add
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_initPart_smul
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
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (h0 : LL.deg (Fin.last K) = 0) : DivModP p LL J M ρ := by
  intro h hY hI a ha b hb he
  have hsupp : ∀ m ∈ h.support, m (Fin.last K, ρ) = 0 := by
    intro m hm
    have hP : h ∈ Pol p r LL := (Submodule.mem_inf.1 hY).1
    have hmd : MultiDeg LL m := ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hP) hm
    have hs : ∑ c, m (Fin.last K, c) = 0 := by rw [hmd (Fin.last K), h0]
    exact (Finset.sum_eq_zero_iff.1 hs) ρ (Finset.mem_univ _)
  have hinit : initPart (Fin.last K, ρ) 0 h = h := by
    ext m
    rw [coeff_initPart]
    split_ifs with hm
    · rfl
    · symm
      by_contra hne
      exact hm (hsupp m (MvPolynomial.mem_support_iff.2 hne))
  have hXa : initPart (Fin.last K, ρ) 0 (X (Fin.last K, ρ) * a) = 0 := by
    ext m
    rw [coeff_initPart, MvPolynomial.coeff_zero]
    split_ifs with hm
    · simp [MvPolynomial.coeff_X_mul', Finsupp.mem_support_iff, hm]
    · rfl
  have hbI : initPart (Fin.last K, ρ) 0 b ∈ IntPol p (Fin (K + 1) × Fin r) := by
    obtain ⟨b0, hb0⟩ := LinearMap.mem_range.1 hb
    refine LinearMap.mem_range.2 ⟨∑ m ∈ b0.support,
      if m (Fin.last K, ρ) = 0 then monomial m (MvPolynomial.coeff m b0) else 0, ?_⟩
    rw [← hb0]
    change MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) (∑ m ∈ b0.support,
        if m (Fin.last K, ρ) = 0 then monomial m (MvPolynomial.coeff m b0) else 0)
      = initPart (Fin.last K, ρ) 0 (MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p]) b0)
    unfold initPart
    rw [MvPolynomial.support_map_of_injective _ (f := algebraMap ℤ_[p] ℚ_[p]) (fun a b h => Subtype.ext h),
      map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp [MvPolynomial.map_monomial, MvPolynomial.coeff_map]
  refine ⟨0, Submodule.zero_mem _, initPart (Fin.last K, ρ) 0 b, hbI, ?_, ?_⟩
  · rw [mul_zero]
    exact Submodule.zero_mem _
  · rw [mul_zero, zero_add]
    calc h = initPart (Fin.last K, ρ) 0 h := hinit.symm
      _ = _ := by rw [he, initPart_add, initPart_smul, hXa, zero_add]
end Formalism.InvariantFactorPaths.L4
