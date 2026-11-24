-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_E_un
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:25.351866+00:00
-- url     : https://prove2.me/submissions/f16bb886-f0d6-48ec-b0ca-764d670820b5

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
import Theorems.Thm_Formalism_UG_P_fIwasawa_E_mulVec
import Theorems.Thm_Formalism_UG_P_fIwasawa_un_of_isometry


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (e z : Fin n → L) (c : L)
    (hee : fIwasawaH σ e e = 0) (hez : fIwasawaH σ e z = 0)
    (hc : c + σ c + fIwasawaH σ z z = 0) : fIwasawaUn σ (fIwasawaE σ e z c) := by
  have Hal : ∀ x x' y : Fin n → L, fIwasawaH σ (x + x') y = fIwasawaH σ x y + fIwasawaH σ x' y := by
    intro x x' y
    simp [fIwasawaH, add_mul, Finset.sum_add_distrib]
  have Hsl : ∀ x x' y : Fin n → L, fIwasawaH σ (x - x') y = fIwasawaH σ x y - fIwasawaH σ x' y := by
    intro x x' y
    simp [fIwasawaH, sub_mul, Finset.sum_sub_distrib]
  have Hml : ∀ (t : L) (x y : Fin n → L), fIwasawaH σ (t • x) y = σ t * fIwasawaH σ x y := by
    intro t x y
    simp [fIwasawaH, Finset.mul_sum, mul_assoc]
  have Har : ∀ x y y' : Fin n → L, fIwasawaH σ x (y + y') = fIwasawaH σ x y + fIwasawaH σ x y' := by
    intro x y y'
    simp [fIwasawaH, mul_add, Finset.sum_add_distrib]
  have Hsr : ∀ x y y' : Fin n → L, fIwasawaH σ x (y - y') = fIwasawaH σ x y - fIwasawaH σ x y' := by
    intro x y y'
    simp [fIwasawaH, mul_sub, Finset.sum_sub_distrib]
  have Hmr : ∀ (t : L) (x y : Fin n → L), fIwasawaH σ x (t • y) = t * fIwasawaH σ x y := by
    intro t x y
    simp only [fIwasawaH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have Hsym : ∀ x y : Fin n → L, fIwasawaH σ y x = σ (fIwasawaH σ x y) := by
    intro x y
    simp only [fIwasawaH, map_sum, map_mul, hσ]
    exact (Fintype.sum_equiv Fin.revPerm _ _ fun j => by simp [mul_comm]).symm
  apply fIwasawa_un_of_isometry
  intro w w'
  rw [fIwasawa_E_mulVec, fIwasawa_E_mulVec]
  simp only [Hal, Hsl, Hml, Har, Hsr, Hmr, map_mul]
  simp only [Hsym z w, Hsym e w, Hsym e z, hez, hee, map_zero]
  linear_combination (σ (fIwasawaH σ e w) * fIwasawaH σ e w') * hc
end Formalism.UG.P
