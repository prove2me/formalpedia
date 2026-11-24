-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.eq_zero_of_EW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:51.735709+00:00
-- url     : https://prove2.me/submissions/eabde48c-0060-4d05-9242-813b25bd9bb4

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
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


section
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {R σ : Type} [CommSemiring R]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]
variable {r : ℕ} (w e : Fin r → σ)
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
private theorem X_mul_pderiv_monomial_lemma_3 (v : σ) (t : σ →₀ ℕ) (c : k) :
    X v * pderiv v (monomial t c) = monomial t (c * (t v : k)) := by
  classical
  rw [pderiv_monomial]
  by_cases ht : t v = 0
  · simp [ht]
  · rw [MvPolynomial.X, monomial_mul, one_mul]
    have h1 : Finsupp.single v 1 + (t - Finsupp.single v 1) = t := by
      ext x
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs with hx
      · subst hx; omega
      · omega
    rw [h1]
private theorem coeff_X_mul_pderiv_lemma_4 (v : σ) (g : MvPolynomial σ k) (s : σ →₀ ℕ) :
    coeff s (X v * pderiv v g) = (s v : k) * coeff s g := by
  classical
  induction g using MvPolynomial.induction_on'
  · rename_i t c
    rw [X_mul_pderiv_monomial_lemma_3, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  · rename_i p q hp hq
    rw [map_add, mul_add, coeff_add, hp, hq, coeff_add]; ring
private theorem coeff_EW_lemma_5 (g : MvPolynomial σ k) (s : σ →₀ ℕ) :
    coeff s (EW w g) = ((∑ c, s (w c) : ℕ) : k) * coeff s g := by
  rw [EW, coeff_sum]
  simp only [coeff_X_mul_pderiv_lemma_4, Nat.cast_sum, Finset.sum_mul]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open Polynomial Finset
section
variable {k : Type} [Field k] [CharZero k]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open Finset
section
variable {k : Type} [Field k] [CharZero k]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {R σ : Type} [CommSemiring R]
end
section
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end
section
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
end
section
variable (p : ℕ) [Fact p.Prime]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM
open MvPolynomial Finset
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (a b : ℕ) (hab : a < b) (g : MvPolynomial σ k) (h : EW w g = ((a : k) - b) • g) :
    g = 0 := by
  ext s
  have hs := congrArg (coeff s) h
  rw [coeff_EW_lemma_5, coeff_smul, smul_eq_mul] at hs
  have hne : ((∑ c, s (w c) : ℕ) : k) ≠ (a : k) - b := by
    intro heq
    have h2 : ((∑ c, s (w c) + b : ℕ) : k) = ((a : ℕ) : k) := by rw [Nat.cast_add, heq]; ring
    have h3 := Nat.cast_injective h2
    omega
  rw [coeff_zero]
  by_contra hc
  exact hne (mul_right_cancel₀ hc hs)
end Formalism.GM.GammaExpansion
