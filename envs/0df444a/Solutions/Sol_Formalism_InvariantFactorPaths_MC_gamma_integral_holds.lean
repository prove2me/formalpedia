-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.MC.gamma_integral_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:06:58.923215+00:00
-- url     : https://prove2.me/submissions/6bf14b66-6290-4ced-a44a-421cd9dfc361

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMCB
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_GamIntC
import Theorems.Thm_Formalism_InvariantFactorPaths_MC_GI_termF_IVPE
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_sum
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
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_FT_pow_coeff_norm
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_toChoose
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_aeval_good
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_aeval_int
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_deg_le_total
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_intPol_coeff
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_supp_FT_pow
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_tieGam_expand
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas__v_add_9b2e3af02dc8
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas__v_single_a5388cd8d2f0
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas_zpow_mono__fc2d0d98fdd7
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.MC
open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.gammaIntegralityLemmas Formalism.InvariantFactorPaths.MC.GI
namespace Formalism.InvariantFactorPaths.MC
theorem _root_.solution : GamIntC := by
  intro p _ N r LL ρ z f f' hr hW hf hf'
  set B := Nat.log p (LL.total + LL.deg (Fin.last N) + r) with hB
  have hκ : (N + 4) * (r * B) + 6 * B = kapE N r B := rfl
  have hwe : ∀ c : Fin r, wv (N := N) c ≠ ev c := by
    intro c; simp [wv, ev, Fin.castSucc_ne_last]

  have facts : ∀ g : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p], g ∈ PolZ p r LL →
      (∀ b ≤ LL.total + LL.deg (Fin.last N) + r, ∀ β,
        ‖coeff β ((FT wv ev (univ.erase ρ) ^ b) (aeval (freezeSub p LL ρ) g))‖ ≤
          (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p b.factorial : ℤ)))) ∧
      (∀ b, ∀ β ∈ ((FT wv ev (univ.erase ρ) ^ b) (aeval (freezeSub p LL ρ) g)).support,
        δv β + b • eWY = (LL.snoc LL.total).deg ∧ β (xW ρ) ≤ β (yE ρ)) := by
    intro g hg
    have hgP : g ∈ Pol p r LL := (Submodule.mem_inf.mp hg).1
    have hgI : g ∈ IntPol p (Fin (N + 1) × Fin r) := (Submodule.mem_inf.mp hg).2
    have hG := aeval_int LL ρ g (intPol_coeff g hgI)
    have hGg := aeval_good LL ρ hW g hgP
    refine ⟨fun b hb β => ?_, ?_⟩
    · have h1 := FT_pow_coeff_norm (p := p) wv ev hwe (LL.total + LL.deg (Fin.last N) + r) B le_rfl 1
        (aeval (freezeSub p LL ρ) g) hG (univ.erase ρ) b hb β
      refine h1.trans ?_
      rw [one_mul]
      apply zpow_mono'
      have : (univ.erase ρ).card * B ≤ r * B := by
        apply Nat.mul_le_mul_right
        rw [card_erase_of_mem (mem_univ ρ), card_univ, Fintype.card_fin]; omega
      have : (((univ.erase ρ).card * B : ℕ) : ℤ) ≤ ((r * B : ℕ) : ℤ) := by exact_mod_cast this
      linarith
    · refine supp_FT_pow wv ev (univ.erase ρ)
        (fun b β => δv β + b • eWY = (LL.snoc LL.total).deg ∧ β (xW ρ) ≤ β (yE ρ)) ?_ hwe _ ?_
      · intro b β c hc ⟨h1, h2⟩
        have hcρ : c ≠ ρ := ne_of_mem_erase hc
        refine ⟨?_, ?_⟩
        · rw [← h1, δv_add, δv_add, δv_single, δv_single, succ_nsmul, eWY]
          abel
        · simpa [Finsupp.single_apply, xW, yE, wv, ev, hcρ, Ne.symm hcρ, Fin.castSucc_ne_last] using h2
      · intro β hβ
        obtain ⟨h1, h2⟩ := hGg β hβ
        exact ⟨by rw [zero_smul, add_zero]; exact h1, h2⟩
  obtain ⟨hc1, hs1⟩ := facts f hf
  obtain ⟨hc2, hs2⟩ := facts f' hf'
  have hIVP : IVP p (LL.total + LL.deg (Fin.last N))
      (fun m => (p : ℚ_[p]) ^ (kapE N r B) * tieGam p LL ρ z (m + LL.total) f f') := by
    simp only [tieGam_expand, Finset.mul_sum]
    apply IVP.sum; intro j hj
    apply IVP.sum; intro a ha
    apply IVP.sum; intro a' ha'
    apply IVP.sum; intro β hβ
    apply IVP.sum; intro γ hγ
    rw [mem_range] at hj ha ha'
    have hjo : j ≤ LL.deg (Fin.last N) := by omega
    have hoS := deg_le_total LL (Fin.last N)
    obtain ⟨hβd, hβp⟩ := hs1 (j - a) β hβ
    obtain ⟨hγd, hγp⟩ := hs2 (j - a') γ hγ
    exact termF_IVPE LL ρ hr B le_rfl z j a a' hjo (by omega) (by omega) β γ hβd hβp hγd hγp _ _
      (hc1 (j - a) (by omega) β) (hc2 (j - a') (by omega) γ)
  obtain ⟨c, hc⟩ := hIVP.toChoose (S := LL.total)
  refine ⟨c, fun n hn => ?_⟩
  have := hc n hn
  simp only [Nat.sub_add_cancel hn] at this
  rw [hκ]
  exact this
end Formalism.InvariantFactorPaths.MC
