-- Prove2me | solution 1 for Erdos393Proof.poly_shape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:33:24.558739+00:00
-- url     : https://prove2.me/submissions/da0925eb-7ff7-4d3b-b7fc-4e7d822380e8

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial
namespace Erdos393Proof
theorem _root_.solution (T : Finset ℕ) (h0 : 0 ∈ T) {m : ℕ} (hm : m ∈ T) (hm0 : m ≠ 0) :
    ∃ (k : ℕ) (R : ℤ[X]), R.eval 0 ≠ 0 ∧ k + R.natDegree + 2 ≤ T.card ∧ ∀ a : ℕ,
      ((T.card * a + ∑ i ∈ T, i : ℕ) : ℤ) ^ T.card +
        ((T.card * a + ∑ i ∈ T, i : ℕ) : ℤ) ^ k * R.eval ((T.card * a + ∑ i ∈ T, i : ℕ) : ℤ) =
      (T.card : ℤ) ^ T.card * ((∏ i ∈ T, (a + i) : ℕ) : ℤ) := by
  have hd2 : 2 ≤ T.card := Finset.one_lt_card.2 ⟨0, h0, m, hm, fun h ↦ hm0 h.symm⟩
  set d := T.card with hd
  set e : ℤ := ((∑ i ∈ T, i : ℕ) : ℤ) with he
  set P : ℤ[X] := ∏ i ∈ T, (X - C (e - d * (i : ℤ))) with hP
  have hmon : ∀ i ∈ T, (X - C (e - d * (i : ℤ))).Monic := fun i _ ↦ monic_X_sub_C _
  have hPmonic : P.Monic := monic_prod_of_monic _ _ hmon
  have hPdeg : P.natDegree = d := by
    rw [hP, natDegree_prod_of_monic _ _ hmon]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, hd]
  have hsum : ∑ i ∈ T, (e - d * (i : ℤ)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, he, hd]
    push_cast
    ring
  have hnext : P.coeff (d - 1) = 0 := by
    have h : P.nextCoeff = -∑ i ∈ T, (e - d * (i : ℤ)) := prod_X_sub_C_nextCoeff _
    rw [nextCoeff_of_natDegree_pos (by rw [hPdeg]; omega), hPdeg, hsum, neg_zero] at h
    exact h
  set Q : ℤ[X] := P - X ^ d with hQ
  have hQdeg : Q.natDegree ≤ d - 2 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hQ, coeff_sub, coeff_X_pow]
    rcases (show N = d - 1 ∨ N = d ∨ d < N by omega) with rfl | rfl | hlt
    · rw [if_neg (by omega), hnext, sub_zero]
    · rw [if_pos rfl, ← hPdeg, hPmonic.coeff_natDegree, sub_self]
    · rw [if_neg (by omega), coeff_eq_zero_of_natDegree_lt (by rw [hPdeg]; exact hlt),
        sub_zero]
  have hQ0 : Q ≠ 0 := by
    intro hQz
    have hPX : P = X ^ d := sub_eq_zero.1 hQz
    have hev : P.eval e = 0 := by
      rw [hP, eval_prod]
      exact Finset.prod_eq_zero h0 (by simp)
    rw [hPX, eval_pow, eval_X] at hev
    have he0 : e = 0 := (pow_eq_zero_iff (by omega)).1 hev
    have hme : (m : ℤ) ≤ e := by
      rw [he]
      exact_mod_cast Finset.single_le_sum (fun i _ ↦ Nat.zero_le i) hm
    omega
  obtain ⟨R, hQR, hRX⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ0 0
  rw [map_zero, sub_zero] at hQR hRX
  have hR0 : R.eval 0 ≠ 0 := by rwa [X_dvd_iff, coeff_zero_eq_eval_zero] at hRX
  have hRne : R ≠ 0 := by
    rintro rfl
    exact hR0 (eval_zero)
  have hQdeg' : Q.natDegree = Q.rootMultiplicity 0 + R.natDegree := by
    conv_lhs => rw [hQR]
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hRne, natDegree_X_pow]
  refine ⟨Q.rootMultiplicity 0, R, hR0, by omega, fun a ↦ ?_⟩
  set y : ℤ := ((d * a + ∑ i ∈ T, i : ℕ) : ℤ) with hy
  have hPy : P.eval y = (d : ℤ) ^ d * ((∏ i ∈ T, (a + i) : ℕ) : ℤ) := by
    rw [hP, eval_prod]
    calc ∏ i ∈ T, eval y (X - C (e - d * (i : ℤ))) = ∏ i ∈ T, ((d : ℤ) * ((a + i : ℕ) : ℤ)) :=
          Finset.prod_congr rfl fun i _ ↦ by
            rw [eval_sub, eval_X, eval_C, hy, he]
            push_cast
            ring
      _ = (d : ℤ) ^ d * ((∏ i ∈ T, (a + i) : ℕ) : ℤ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← hd]
        push_cast
        rfl
  have hQy : Q.eval y = y ^ Q.rootMultiplicity 0 * R.eval y := by
    conv_lhs => rw [hQR]
    rw [eval_mul, eval_pow, eval_X]
  have hQP : Q.eval y = P.eval y - y ^ d := by rw [hQ, eval_sub, eval_pow, eval_X]
  rw [← hPy]
  linear_combination hQP - hQy
end Erdos393Proof
