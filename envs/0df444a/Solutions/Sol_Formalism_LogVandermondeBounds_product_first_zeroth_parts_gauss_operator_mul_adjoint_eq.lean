-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.gauss_operator_mul_adjoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:37:49.79183+00:00
-- url     : https://prove2.me/submissions/d4c0cf09-9b7d-47f6-9bb5-8603d5a462fe

import Definitions.Def_Formalism_LogVandermondeBounds_GaussOperatorProductFormula
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_FourierIsometryOnNormKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
section Helpers
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}
private lemma conj_char (ψ : AddChar k ℂ) (a : k) : (starRingEnd ℂ) (ψ a) = ψ (-a) := by
  have hR : 0 < ringChar k := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite k)
  rw [AddChar.starComp_apply hR, AddChar.inv_apply]
private lemma sum_eq_zero_of_shift {G : Type*} [AddCommGroup G] [Fintype G] (F : G → ℂ) (y : G) (b : ℂ)
    (hb : b ≠ 1) (h : ∀ x, F (y + x) = b * F x) : ∑ x, F x = 0 := by
  refine eq_zero_of_mul_eq_self_left hb ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft y) _ _ (fun x => (h x).symm)
private lemma sum_char_mul (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (a : k) :
    ∑ t, ψ (a * t) = if a = 0 then (Fintype.card k : ℂ) else 0 := by
  split_ifs with ha
  · simp [ha]
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.1 hψ
  refine sum_eq_zero_of_shift (fun t => ψ (a * t)) (a⁻¹ * x) (ψ x) hx (fun t => ?_)
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ ha, one_mul, AddChar.map_add_eq_mul]
private lemma sum_units (F : k → ℂ) : ∑ c : kˣ, F (c : k) = ∑ t, F t - F 0 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : k)), add_sub_cancel_right]
  refine Finset.sum_bij' (fun c _ => (c : k)) (fun t ht => if h : t = 0 then 1 else Units.mk0 t h)
    ?_ ?_ ?_ ?_ ?_
  · intro c _; simp [Units.ne_zero]
  · intro t _; simp
  · intro c _; simp [Units.ne_zero]
  · intro t ht
    have : t ≠ 0 := Finset.ne_of_mem_erase ht
    simp [this]
  · intro c _; rfl
end Helpers
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
end

set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution : GaussOperatorProductFormula := by
  intro k _ _ _ r ψ hψ φ f
  have h1 : opGs ψ (opGsStar ψ φ) f =
      ∑ d : kˣ, ∑ u : kˣ, ψ ((u : k) * d) * ψ (-(d : k)) * φ ((u : k) • f) := by
    simp only [opGs, opGsStar, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    refine Fintype.sum_equiv (Equiv.mulRight d⁻¹) _ _ (fun c => ?_)
    simp only [Equiv.coe_mulRight, Units.val_mul, conj_char, smul_smul, Units.val_inv_eq_inv_val]
    rw [inv_mul_cancel_right₀ (Units.ne_zero d), mul_comm ((d : k)⁻¹) (c : k), mul_assoc]
  have h2 : ∀ u : kˣ, ∑ d : kˣ, ψ ((u : k) * d) * ψ (-(d : k)) =
      (if (u : k) - 1 = 0 then (Fintype.card k : ℂ) else 0) - 1 := by
    intro u
    have := sum_units (fun t => ψ (((u : k) - 1) * t))
    simp only [mul_zero, AddChar.map_zero_eq_one] at this
    rw [← sum_char_mul ψ hψ, ← this]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [h1, Finset.sum_comm]
  have h3 : ∀ u : kˣ, ∑ d : kˣ, ψ ((u : k) * d) * ψ (-(d : k)) * φ ((u : k) • f) =
      φ ((u : k) • f) * ((if (u : k) - 1 = 0 then (Fintype.card k : ℂ) else 0) - 1) := by
    intro u
    rw [← h2 u, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [Finset.sum_congr rfl (fun u _ => h3 u)]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sub_eq_zero, Units.val_eq_one, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Units.val_one, one_smul]
  simp [nmP, diaP, mul_comm]
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
