-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.fourier_transform_kernel_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:45.206123+00:00
-- url     : https://prove2.me/submissions/e9f4f703-7128-4036-be4d-79a2265fd0aa

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.LocalLatticeBases
open Finset Matrix
section Count
variable {F : Type} [Field F]
variable [Fintype F]
end Count
section FJ
variable {F : Type} [Field F] [Fintype F]
end FJ
section Onto
open Formalism.LogVandermondeBounds.product_first_zeroth_parts
section FFOnto
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}
private lemma pair_smul_left_hook_formula_torsion (a : k) (f x : Fin r → k) : pair (a • f) x = a * pair f x := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
private lemma pair_smul_right' (a : k) (f x : Fin r → k) : pair f (a • x) = a * pair f x := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)
private lemma pair_add_left' (f g x : Fin r → k) : pair (f + g) x = pair f x + pair g x := by
  simp only [pair, Pi.add_apply, add_mul, Finset.sum_add_distrib]
private lemma pairing_sub_right (f x y : Fin r → k) : pair f (x - y) = pair f x - pair f y := by
  simp only [pair, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
private lemma pair_zero_right' (f : Fin r → k) : pair f (0 : Fin r → k) = 0 := by
  simp [pair]
private lemma pairing_single_left (x : Fin r → k) (i : Fin r) (a : k) :
    pair (Pi.single i a) x = a * x i := by
  simp [pair, Pi.single_apply]
private lemma unit_smul_equiv_apply (c : kˣ) (f : Fin r → k) :
    unitSmulEquiv c f = (c : k) • f := rfl
private lemma sum_eq_zero_of_twisted_shift {G : Type*} [AddCommGroup G] [Fintype G] (F : G → ℂ) (y : G)
    (b : ℂ) (hb : b ≠ 1) (h : ∀ x, F (y + x) = b * F x) : ∑ x, F x = 0 := by
  refine eq_zero_of_mul_eq_self_left hb ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft y) _ _ (fun x => (h x).symm)
private lemma sum_char_pairing_orthogonality (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (h : Fin r → k) :
    ∑ f, ψ (pair f h) = if h = 0 then (Fintype.card k : ℂ) ^ r else 0 := by
  split_ifs with hh
  · subst hh
    simp [pair_zero_right']
  obtain ⟨i, hi'⟩ := Function.ne_iff.1 hh
  have hi : h i ≠ 0 := hi'
  obtain ⟨x0, hx0⟩ := AddChar.ne_one_iff.1 hψ
  refine sum_eq_zero_of_twisted_shift (fun f => ψ (pair f h)) (Pi.single i (x0 * (h i)⁻¹)) (ψ x0) hx0
    (fun f => ?_)
  rw [pair_add_left', pairing_single_left, mul_assoc, inv_mul_cancel₀ hi, mul_one,
    AddChar.map_add_eq_mul]
end FFOnto
end Onto
end Formalism.HermitianLattices.LocalLatticeBases
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset Matrix
open Formalism.LogVandermondeBounds.product_first_zeroth_parts
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : Formalism.HermitianLattices.LocalLatticeBases.FourierTransformKernelSurjective := by
  intro k _ _ _ r ψ hψ ψv hv
  set v0 : (Fin r → k) → ℂ := fun x => if x = 0 then 0 else ψv x with hv0
  have hq : (Fintype.card k : ℂ) ^ r ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  have hnm0 : ∀ y, ∑ c : kˣ, v0 (((c⁻¹ : kˣ) : k) • y) = 0 := by
    intro y
    by_cases hy : y = 0
    · simp [hy, hv0]
    · have := hv y hy
      simp only [nmV, diaV] at this
      rw [← this]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      simp [hv0, hy]
  let φ : (Fin r → k) → ℂ :=
    fun f => ((Fintype.card k : ℂ) ^ r)⁻¹ * ∑ x, ψ (-pair f x) * v0 x
  have hnm : ∀ f, nmP φ f = 0 := by
    intro f
    simp only [nmP, diaP, φ]
    rw [← Finset.mul_sum]
    have key : ∑ c : kˣ, ∑ x, ψ (-pair ((c : k) • f) x) * v0 x = 0 := by
      have step : ∀ c : kˣ, ∑ x, ψ (-pair ((c : k) • f) x) * v0 x =
          ∑ y, ψ (-pair f y) * v0 (((c⁻¹ : kˣ) : k) • y) := by
        intro c
        refine Fintype.sum_equiv (unitSmulEquiv c) _ _ (fun x => ?_)
        simp only [unit_smul_equiv_apply, pair_smul_left_hook_formula_torsion, pair_smul_right', smul_smul,
          Units.inv_mul, one_smul]
      rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]
      refine Finset.sum_eq_zero (fun y _ => ?_)
      rw [← Finset.mul_sum, hnm0, mul_zero]
    rw [key, mul_zero]
  have hφ0 : φ 0 = 0 := by
    have := hnm 0
    simp only [nmP, diaP, smul_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  refine ⟨φ, fun f _ => hnm f, fun x hx => ?_⟩
  have h1 : opFF ψ φ x = ∑ f, ψ (pair f x) * φ f := by
    simp only [opFF, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    by_cases hf : f = 0
    · simp [hf, hφ0]
    · simp [hf]
  have h2 : ∑ f, ψ (pair f x) * φ f =
      ((Fintype.card k : ℂ) ^ r)⁻¹ * ∑ y, v0 y * ∑ f, ψ (pair f (x - y)) := by
    simp only [φ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun f _ => ?_))
    rw [pairing_sub_right, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  rw [h1, h2]
  simp only [sum_char_pairing_orthogonality ψ hψ, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [hv0, hx, Finset.mem_univ, if_true, if_false]
  field_simp
end Formalism.HermitianLattices.LocalLatticeBases
