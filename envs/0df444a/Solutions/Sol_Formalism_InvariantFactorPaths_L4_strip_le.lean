-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.strip_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:23:13.824393+00:00
-- url     : https://prove2.me/submissions/9a7f61e4-7c7a-4ff4-987c-cbc88ede7b5a

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_phiW_shift
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_cw_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eW_pow_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_shiftN_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_shiftN_back
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_shiftN_one
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eJ_cw_diag
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eJ_pow_cw
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_nil
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_comm
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_sl2_injectivity_holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Cs : Finset (Fin r)) (th : Fin r → ℤ)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ HWC p LL (K + 1) Cs th) (β : Fin r → ℤ)
    (hy : cw p K β x ≠ 0) (htop : ∀ γ, phiW β < phiW γ → cw p K γ x = 0) (hβ : ∀ c, 0 ≤ β c)
    (a a' : Fin r) (ha : a ∈ Cs) (ha' : a' ∈ Cs) (haa : a < a') : th a' ≤ th a - β a := by
  by_contra hcon
  have hne : a ≠ a' := ne_of_lt haa
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = β a' := ⟨(β a').toNat, Int.toNat_of_nonneg (hβ a')⟩
  set u := cw p K (shiftN β a a' k) x with hu
  have hpk := eJ_pow_cw LL hv Cs th x hx a a' ha ha' haa k (shiftN β a a' k)
  rw [shiftN_back, sub_self, shiftN_zero] at hpk
  have hu0 : u ≠ 0 := by
    intro h0
    rw [← hu, h0, map_zero] at hpk
    rcases smul_eq_zero.mp hpk.symm with h1 | h1
    · exact absurd h1 (pow_ne_zero _ (by norm_num))
    · exact eW_pow_ne a a' hne k β _ (cw_mem β x) hy (le_of_eq hk) (hβ a) h1
  have hpk1 := eJ_pow_cw LL hv Cs th x hx a a' ha ha' haa (k + 1) (shiftN β a a' k)
  have e1 : shiftN (shiftN β a a' k) a' a ((k + 1 : ℕ) : ℤ) = shiftW β a' a := by
    rw [shiftN_back, ← shiftN_one]; congr 1; push_cast; ring
  rw [e1, htop (shiftW β a' a) (by
    rw [phiW_shift]
    have : ((a : ℕ) : ℤ) < ((a' : ℕ) : ℤ) := by exact_mod_cast haa
    omega), map_zero, smul_zero] at hpk1
  have hd1 := eJ_cw_diag LL hv Cs th x hx a ha (shiftN β a a' k)
  have hd2 := eJ_cw_diag LL hv Cs th x hx a' ha' (shiftN β a a' k)
  have hh : (glAct p LL K a a - glAct p LL K a' a') u =
      (((th a - β a - k) - (th a' - β a' + k) : ℤ) : ℚ_[p]) • u := by
    rw [LinearMap.sub_apply, hu, hd1, hd2, ← sub_smul]
    congr 1
    simp only [shiftN, if_neg hne, if_neg (Ne.symm hne), if_true]
    push_cast
    ring
  refine hu0 (sl2_injectivity_holds ℚ_[p] _ (glAct p LL K a a') (glAct p LL K a' a) (glAct p LL K a a - glAct p LL K a' a')
    ?_ ?_ ?_ u _ (k + 1) hh (glAct_nil LL K a' a (Ne.symm hne) u) (by push_cast; omega) hpk1)
  · intro z
    have h1 := glAct_comm LL K a a a a' z
    have h2 := glAct_comm LL K a' a' a a' z
    rw [if_pos rfl, if_neg (Ne.symm hne)] at h1
    rw [if_neg (Ne.symm hne), if_pos rfl] at h2
    simp only [LinearMap.sub_apply, map_sub]
    rw [two_smul]
    linear_combination (exp := 1) h1 - h2
  · intro z
    have h1 := glAct_comm LL K a a a' a z
    have h2 := glAct_comm LL K a' a' a' a z
    rw [if_neg hne, if_pos rfl] at h1
    rw [if_pos rfl, if_neg hne] at h2
    simp only [LinearMap.sub_apply, map_sub]
    rw [two_smul]
    linear_combination (exp := 1) h1 - h2
  · intro z
    have h1 := glAct_comm LL K a a' a' a z
    rw [if_pos rfl, if_pos rfl] at h1
    rw [LinearMap.sub_apply]
    exact h1
end Formalism.InvariantFactorPaths.L4
