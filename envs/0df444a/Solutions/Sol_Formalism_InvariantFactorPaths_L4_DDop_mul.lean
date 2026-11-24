-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.DDop_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:15.975568+00:00
-- url     : https://prove2.me/submissions/ed659a97-c3f3-4957-bfdf-92e0f727c981

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
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


section
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
section D
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end D
section U
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
variable (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r)
private theorem sum_linearMaps_leibniz_of_leibniz {σ ι : Type} (s : Finset ι)
    (L : ι → MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (h : ∀ i ∈ s, ∀ f g, L i (f * g) = L i f * g + f * L i g) (f g : MvPolynomial σ ℚ_[p]) :
    (∑ i ∈ s, L i) (f * g) = (∑ i ∈ s, L i) f * g + f * (∑ i ∈ s, L i) g := by
  simp only [LinearMap.sum_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i hi => h i hi f g)
private theorem mulLeft_comp_leibniz_of_leibniz {σ : Type} (q : MvPolynomial σ ℚ_[p])
    (L : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (h : ∀ f g, L (f * g) = L f * g + f * L g) (f g : MvPolynomial σ ℚ_[p]) :
    (LinearMap.mulLeft ℚ_[p] q ∘ₗ L) (f * g) =
      (LinearMap.mulLeft ℚ_[p] q ∘ₗ L) f * g + f * (LinearMap.mulLeft ℚ_[p] q ∘ₗ L) g := by
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, h]
  ring
private theorem pderiv_toLinearMap_mul {σ : Type} (v : σ) (f g : MvPolynomial σ ℚ_[p]) :
    (↑(pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])) :
      MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) (f * g) =
    (↑(pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])) :
      MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) f * g +
    f * (↑(pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])) :
      MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) g := by
  simp only [Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul]
  ring
end U
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
variable (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (f g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    DDop p LL Cs a (f * g) = DDop p LL Cs a f * g + f * DDop p LL Cs a g := by
  have hg : ∀ b, ∀ f g, glAct p LL K a b (f * g) = glAct p LL K a b f * g + f * glAct p LL K a b g := by
    intro b
    unfold glAct
    apply sum_linearMaps_leibniz_of_leibniz
    intro i _
    split_ifs
    · exact mulLeft_comp_leibniz_of_leibniz _ _ (pderiv_toLinearMap_mul _)
    · intro f g
      rw [LinearMap.neg_apply, LinearMap.neg_apply, LinearMap.neg_apply, mulLeft_comp_leibniz_of_leibniz _ _ (pderiv_toLinearMap_mul _)]
      ring
    · intro f g
      simp
  have he : ∀ f g, eulW p K r (f * g) = eulW p K r f * g + f * eulW p K r g := by
    unfold eulW
    apply sum_linearMaps_leibniz_of_leibniz
    intro i _
    exact mulLeft_comp_leibniz_of_leibniz _ _ (pderiv_toLinearMap_mul _)
  have hA : (Wm p K a ∘ₗ eulW p K r) (f * g) =
      (Wm p K a ∘ₗ eulW p K r) f * g + f * (Wm p K a ∘ₗ eulW p K r) g := mulLeft_comp_leibniz_of_leibniz _ _ he f g
  have hs : (∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b) (f * g) =
      (∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b) f * g + f * (∑ b ∈ Cs, Wm p K b ∘ₗ glAct p LL K a b) g :=
    sum_linearMaps_leibniz_of_leibniz Cs (fun b => Wm p K b ∘ₗ glAct p LL K a b) (fun b _ => mulLeft_comp_leibniz_of_leibniz _ _ (hg b)) f g
  unfold DDop
  simp only [LinearMap.add_apply]
  rw [hA, hs]
  ring
end Formalism.InvariantFactorPaths.L4
