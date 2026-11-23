-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.q_isWH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:37.202848+00:00
-- url     : https://prove2.me/submissions/ac0eec74-8068-45d1-b17e-f5c64c3e1447

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_mul
import Theorems.Thm_Formalism_GM_GammaExpansion_IsPD_sum
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
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ) (h : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])
    (hh : h ∈ M.Pol p r (lowerLast LL e)) (g : Fin (N + 1 + 1) → ℕ) :
    IsWeightedHomogeneous (fun y : Fin (N + 1 + 1) × Fin r => g y.1) (aeval (M.freezeSub p LL ρ) h)
      (∑ b, (g (Fin.castSucc b) + g (Fin.last (N + 1))) * (lowerLast LL e).deg b) := by
  classical
  have hXX : ∀ (i : Fin (N + 1)) (c₁ c₂ : Fin r), IsWeightedHomogeneous (fun y : Fin (N + 1 + 1) × Fin r => g y.1)
      (X (Fin.castSucc i, c₁) * X (Fin.last (N + 1), c₂) : MvPolynomial (Fin (N + 1 + 1) × Fin r) ℚ_[p])
      (g (Fin.castSucc i) + g (Fin.last (N + 1))) := fun i c₁ c₂ =>
    (isWeightedHomogeneous_X ℚ_[p] _ _).mul (isWeightedHomogeneous_X ℚ_[p] _ _)
  have hXX' : ∀ (i : Fin (N + 1)) (c₁ c₂ : Fin r), IsWeightedHomogeneous (fun y : Fin (N + 1 + 1) × Fin r => g y.1)
      (X (Fin.last (N + 1), c₂) * X (Fin.castSucc i, c₁) : MvPolynomial (Fin (N + 1 + 1) × Fin r) ℚ_[p])
      (g (Fin.castSucc i) + g (Fin.last (N + 1))) := fun i c₁ c₂ => by
    rw [mul_comm]; exact hXX i c₁ c₂
  have hgen : ∀ x : Fin (N + 1) × Fin r, IsWeightedHomogeneous (fun y : Fin (N + 1 + 1) × Fin r => g y.1)
      (M.freezeSub p LL ρ x) (g (Fin.castSucc x.1) + g (Fin.last (N + 1))) := by
    rintro ⟨i, c⟩
    simp only [M.freezeSub]
    split_ifs
    · exact IsWeightedHomogeneous.sum _ _ _ fun c' _ => hXX i c' c'
    · exact hXX' i c ρ
    · exact hXX' i ρ ρ
    · intro d hd
      rw [coeff_sub] at hd
      by_cases h1 : coeff d (X (Fin.last (N + 1), ρ) * X (Fin.castSucc i, c) :
          MvPolynomial (Fin (N + 1 + 1) × Fin r) ℚ_[p]) = 0
      · rw [h1, zero_sub, neg_ne_zero] at hd
        exact hXX i ρ c hd
      · exact hXX' i c ρ h1
  have hsupp : ∀ m ∈ h.support, M.MultiDeg (lowerLast LL e) m := by
    have h2 := hh
    simp only [M.Pol, MvPolynomial.mem_restrictSupport_iff] at h2
    exact fun m hm => h2 hm
  rw [h.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  rw [aeval_monomial]
  have hmd := hsupp m hm
  have hprod := IsWeightedHomogeneous.prod m.support (fun x => M.freezeSub p LL ρ x ^ m x)
    (fun x => m x • (g (Fin.castSucc x.1) + g (Fin.last (N + 1)))) (fun x _ => (hgen x).pow (m x))
  have hC := isWeightedHomogeneous_C (fun y : Fin (N + 1 + 1) × Fin r => g y.1) (coeff m h)
  have key : ∑ b, (g (Fin.castSucc b) + g (Fin.last (N + 1))) * (lowerLast LL e).deg b =
      0 + ∑ x ∈ m.support, m x • (g (Fin.castSucc x.1) + g (Fin.last (N + 1))) := by
    rw [zero_add, Finset.sum_subset (Finset.subset_univ m.support) (fun x _ hx => by
      rw [Finsupp.mem_support_iff, not_not] at hx; simp [hx])]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hmd b, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [smul_eq_mul, mul_comm]
  rw [key]
  exact hC.mul hprod
end Formalism.GM.GammaExpansion
