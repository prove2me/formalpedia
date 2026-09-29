-- Prove2me | solution 1 for EulerMascheroni.Rivoal.bInt_cast
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T21:29:25.998443+00:00
-- url     : https://prove2.me/submissions/32d70107-9e08-4688-82b4-159aa1076207

import Definitions.Def_eulerMascheroni_rivoalPoly
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

noncomputable section
namespace EulerMascheroni.Rivoal.PolyAux
open Polynomial Finset

lemma beta_dvd (n j : ℕ) (hj : j ≤ n) :
    (j.factorial * (n - j).factorial) ^ 2 ∣ (3 * n - j).factorial := by
  have h1 := Nat.factorial_mul_factorial_dvd_factorial_add n (n - j)
  have h2 := Nat.factorial_mul_factorial_dvd_factorial_add (n + (n - j)) (n - j)
  have h3 := Nat.factorial_mul_factorial_dvd_factorial_add (n + (n - j) + (n - j)) j
  have he : n + (n - j) + (n - j) + j = 3 * n - j := by omega
  rw [he] at h3
  have hA : n.factorial * (n - j).factorial * (n - j).factorial * j.factorial ∣
      (3 * n - j).factorial :=
    (Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right h1 _) _).trans
      ((Nat.mul_dvd_mul_right h2 _).trans h3)
  have hB : (j.factorial * (n - j).factorial) ^ 2 ∣
      n.factorial * (n - j).factorial * (n - j).factorial * j.factorial := by
    have := Nat.mul_dvd_mul_left (j.factorial * (n - j).factorial * (n - j).factorial)
      (Nat.factorial_dvd_factorial hj)
    calc (j.factorial * (n - j).factorial) ^ 2
        = j.factorial * (n - j).factorial * (n - j).factorial * j.factorial := by ring
      _ ∣ j.factorial * (n - j).factorial * (n - j).factorial * n.factorial := this
      _ = _ := by ring
  exact hB.trans hA

theorem bInt_cast (n j : ℕ) (hj : j ≤ n) :
    (bInt n j : ℚ) = (-1) ^ (n - j) * beta n j := by
  unfold bInt beta
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div (beta_dvd n j hj) (by positivity)]
  push_cast; ring

/-- `(3n-j)! = β·(j!(n-j)!)^2` in `ℤ`. -/
lemma bInt_spec (n j : ℕ) (hj : j ≤ n) :
    (-1) ^ (n - j) * bInt n j * ((j.factorial : ℤ) * (n - j).factorial) ^ 2 =
      (3 * n - j).factorial := by
  unfold bInt
  have := Nat.div_mul_cancel (beta_dvd n j hj)
  have h2 : ((-1 : ℤ) ^ (n - j)) * (-1) ^ (n - j) = 1 := by
    rw [← mul_pow]; norm_num
  calc (-1) ^ (n - j) * ((-1) ^ (n - j) * (((3 * n - j).factorial /
        (j.factorial * (n - j).factorial) ^ 2 : ℕ) : ℤ)) * ((j.factorial : ℤ) * (n - j).factorial) ^ 2
      = ((-1 : ℤ) ^ (n - j) * (-1) ^ (n - j)) * ((((3 * n - j).factorial /
        (j.factorial * (n - j).factorial) ^ 2 * (j.factorial * (n - j).factorial) ^ 2 : ℕ) : ℤ)) := by
        push_cast; ring
    _ = _ := by rw [h2, this, one_mul]

lemma descPochhammer_eq_prod (j : ℕ) :
    descPochhammer ℤ j = ∏ i ∈ range j, (X - C (i : ℤ)) := by
  induction j with
  | zero => simp
  | succ k ih => rw [descPochhammer_succ_right, prod_range_succ, ih]; simp

lemma eval_prod_X_sub_C (s : Finset ℕ) (x : ℤ) :
    (∏ i ∈ s, (X - C (i : ℤ))).eval x = ∏ i ∈ s, (x - i) := by
  simp [eval_prod]

/-- `∏_{i<M} (M - i) = M!`. -/
lemma prod_range_sub (M : ℕ) : ∏ i ∈ range M, ((M : ℤ) - i) = M.factorial := by
  have := descPochhammer_eval_eq_descFactorial ℤ M M
  rw [descPochhammer_eq_prod, eval_prod_X_sub_C, Nat.descFactorial_self] at this
  exact this

lemma range_erase_eq (n M : ℕ) (hM : M ≤ n) :
    (range (n + 1)).erase M = range M ∪ Ico (M + 1) (n + 1) := by
  ext i; simp; omega

lemma disj_range_Ico (M n : ℕ) : Disjoint (range M) (Ico (M + 1) (n + 1)) := by
  rw [Finset.disjoint_left]; intro i h1 h2; simp at h1 h2; omega

/-- `δ_M = ∏_{i ≤ n, i ≠ M} (M - i) = (-1)^(n-M) M! (n-M)!`. -/
lemma delta_eq (n M : ℕ) (hM : M ≤ n) :
    ∏ i ∈ (range (n + 1)).erase M, ((M : ℤ) - i) =
      (-1) ^ (n - M) * M.factorial * (n - M).factorial := by
  rw [range_erase_eq n M hM, prod_union (disj_range_Ico M n), prod_range_sub,
    prod_Ico_eq_prod_range]
  have : ∏ k ∈ range (n + 1 - (M + 1)), ((M : ℤ) - ((M + 1 + k : ℕ) : ℤ)) =
      ∏ k ∈ range (n - M), ((-1 : ℤ) * ((k + 1 : ℕ) : ℤ)) := by
    rw [show n + 1 - (M + 1) = n - M by omega]
    refine prod_congr rfl fun k _ => ?_
    push_cast; ring
  rw [this, prod_mul_distrib, prod_const, card_range, ← Nat.cast_prod,
    prod_range_add_one_eq_factorial]
  ring

/-- `N(M) = (3n-M)!/(n-M)!` for `M ≤ n`. -/
lemma polyN_eval_mul (n M : ℕ) (hM : M ≤ n) :
    (polyN n).eval (M : ℤ) * (n - M).factorial = (3 * n - M).factorial := by
  unfold polyN
  rw [eval_prod_X_sub_C]
  have hI : Icc (n + 1) (3 * n) = Ico (n + 1) (3 * n + 1) := rfl
  rw [hI, prod_Ico_eq_prod_range, show 3 * n + 1 - (n + 1) = 2 * n by omega]
  have : ∏ k ∈ range (2 * n), ((M : ℤ) - ((n + 1 + k : ℕ) : ℤ)) =
      ∏ k ∈ range (2 * n), ((-1 : ℤ) * (((n - M) + k + 1 : ℕ) : ℤ)) := by
    refine prod_congr rfl fun k _ => ?_
    push_cast [Nat.cast_sub hM]; ring
  rw [this, prod_mul_distrib, prod_const, card_range, pow_mul]
  norm_num
  have h := prod_range_add (fun x => ((x + 1 : ℕ) : ℤ)) (n - M) (2 * n)
  simp only [← Nat.cast_prod, prod_range_add_one_eq_factorial] at h
  rw [show n - M + 2 * n = 3 * n - M by omega] at h
  rw [h]; push_cast; ring_nf


/-- `δ_M` as a product. -/
abbrev delta (n M : ℕ) : ℤ := ∏ i ∈ (range (n + 1)).erase M, ((M : ℤ) - i)

lemma delta_ne_zero (n M : ℕ) (hM : M ≤ n) : delta n M ≠ 0 := by
  rw [delta, delta_eq n M hM]; positivity

/-- A0: `N(M) = b_M M! δ_M`. -/
lemma polyN_eval_node (n M : ℕ) (hM : M ≤ n) :
    (polyN n).eval (M : ℤ) = bInt n M * M.factorial * delta n M := by
  have hf : ((n - M).factorial : ℤ) ≠ 0 := by positivity
  apply mul_right_cancel₀ hf
  rw [polyN_eval_mul n M hM, delta, delta_eq n M hM, ← bInt_spec n M hM]
  ring

lemma polyU_eval_ne (n j M : ℕ) (hM : M ≤ n) (hjM : j ≠ M) :
    (polyU n j).eval (M : ℤ) = 0 := by
  unfold polyU
  rw [eval_mul, eval_prod_X_sub_C, prod_eq_zero (i := M) (by simp; omega) (by simp), mul_zero]

lemma polyU_eval_self (n M : ℕ) :
    (polyU n M).eval (M : ℤ) = M.factorial * delta n M := by
  unfold polyU
  rw [eval_mul, eval_prod_X_sub_C, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_self]

lemma sum_bU_eval_node (n M : ℕ) (hM : M ≤ n) :
    (∑ j ∈ range (n + 1), C (bInt n j) * polyU n j).eval (M : ℤ) =
      bInt n M * (M.factorial * delta n M) := by
  rw [eval_finsetSum, sum_eq_single M]
  · rw [eval_mul, eval_C, polyU_eval_self]
  · intro j _ hj; rw [eval_mul, polyU_eval_ne n j M hM hj, mul_zero]
  · intro h; simp at h; omega

lemma prod_dvd_of_eval_zero (s : Finset ℕ) (F : ℤ[X]) (h : ∀ i ∈ s, F.eval (i : ℤ) = 0) :
    (∏ i ∈ s, (X - C (i : ℤ))) ∣ F := by
  classical
  induction s using Finset.induction_on generalizing F with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨G, rfl⟩ := ih F (fun i hi => h i (mem_insert_of_mem hi))
    have hFa := h a (mem_insert_self a s)
    rw [eval_mul, eval_prod_X_sub_C] at hFa
    have hp : ∏ i ∈ s, ((a : ℤ) - i) ≠ 0 := by
      rw [prod_ne_zero_iff]; intro i hi h0
      have : (a : ℤ) = i := by linarith
      have : a = i := by exact_mod_cast this
      exact ha (this ▸ hi)
    have hG : G.IsRoot (a : ℤ) := (mul_eq_zero.mp hFa).resolve_left hp
    obtain ⟨K, rfl⟩ := dvd_iff_isRoot.mpr hG
    rw [prod_insert ha]
    exact ⟨K, by ring⟩

lemma polyD_monic (n : ℕ) : (polyD n).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- A3 (polynomial form): `N = P D + ∑ b_j U_j`. -/
theorem polyN_eq_partialFraction (n : ℕ) :
    polyN n = polyP n * polyD n + ∑ j ∈ Finset.range (n + 1), Polynomial.C (bInt n j) * polyU n j := by
  have hdvd : polyD n ∣ polyN n - ∑ j ∈ range (n + 1), C (bInt n j) * polyU n j := by
    apply prod_dvd_of_eval_zero
    intro M hM
    have hM' : M ≤ n := by simp at hM; omega
    rw [eval_sub, sum_bU_eval_node n M hM', polyN_eval_node n M hM']; ring
  have h1 := modByMonic_add_div (polyN n - ∑ j ∈ range (n + 1), C (bInt n j) * polyU n j)
    (polyD n)
  rw [(modByMonic_eq_zero_iff_dvd (polyD_monic n)).mpr hdvd, zero_add] at h1
  unfold polyP
  rw [mul_comm, h1]; ring

lemma natDegree_prod_X_sub_C (s : Finset ℕ) :
    (∏ i ∈ s, (X - C (i : ℤ))).natDegree = s.card := by
  rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
  have : ∀ i ∈ s, (X - C (i : ℤ)).natDegree = 1 := fun i _ => natDegree_X_sub_C _
  rw [sum_congr rfl this]; simp

theorem polyP_natDegree_lt (n : ℕ) (hn : 1 ≤ n) : (polyP n).natDegree < n := by
  have hN : (polyN n).natDegree ≤ 2 * n := by
    unfold polyN; rw [natDegree_prod_X_sub_C]; simp; omega
  have hU : ∀ j ∈ range (n + 1), (C (bInt n j) * polyU n j).natDegree ≤ 2 * n := by
    intro j hj
    simp at hj
    refine (natDegree_C_mul_le _ _).trans ?_
    unfold polyU
    refine (natDegree_mul_le).trans ?_
    rw [descPochhammer_natDegree, natDegree_prod_X_sub_C, card_erase_of_mem (by simp; omega)]
    simp; omega
  have hF := (natDegree_sub_le _ _).trans (max_le hN (natDegree_sum_le_of_forall_le _ _ hU))
  unfold polyP
  rw [natDegree_divByMonic _ (polyD_monic n)]
  have hD : (polyD n).natDegree = n + 1 := by
    unfold polyD; rw [natDegree_prod_X_sub_C]; simp
  omega


/-- A3v. -/
theorem partialFraction_value (n M : ℕ) (hM : n < M) :
    (((polyN n).eval (M : ℤ) : ℤ) : ℚ) / (((polyD n).eval (M : ℤ) : ℤ) : ℚ) =
      (((polyP n).eval (M : ℤ) : ℤ) : ℚ) +
        ∑ j ∈ Finset.range (n + 1), (bInt n j : ℚ) * (M.descFactorial j : ℚ) / ((M : ℚ) - j) := by
  have hD : (((polyD n).eval (M : ℤ) : ℤ) : ℚ) = ∏ i ∈ range (n + 1), ((M : ℚ) - i) := by
    unfold polyD; rw [eval_prod_X_sub_C]; push_cast; rfl
  have hDne : ∏ i ∈ range (n + 1), ((M : ℚ) - i) ≠ 0 := by
    rw [prod_ne_zero_iff]; intro i hi; simp at hi
    have : (i : ℚ) < M := by exact_mod_cast (show i < M by omega)
    linarith
  rw [hD, div_eq_iff hDne, polyN_eq_partialFraction n, eval_add, eval_mul, eval_finsetSum]
  push_cast
  rw [hD, add_mul, sum_mul]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := by simp at hj; omega
  have hq : (M : ℚ) - j ≠ 0 := by
    have : (j : ℚ) < M := by exact_mod_cast (show j < M by omega)
    linarith
  unfold polyU
  rw [eval_mul, eval_C, eval_mul, eval_prod_X_sub_C, descPochhammer_eval_eq_descFactorial,
    ← mul_prod_erase (range (n + 1)) (fun i : ℕ => ((M : ℚ) - i)) hj]
  push_cast
  field_simp

lemma eval_derivative_prod (s : Finset ℕ) (x : ℤ) :
    (derivative (∏ i ∈ s, (X - C (i : ℤ)))).eval x = ∑ i ∈ s, ∏ k ∈ s.erase i, (x - k) := by
  rw [derivative_prod_finset]
  simp [eval_finsetSum, eval_prod]

lemma eval_derivative_prod_root (s : Finset ℕ) (M : ℕ) (hM : M ∈ s) :
    (derivative (∏ i ∈ s, (X - C (i : ℤ)))).eval (M : ℤ) = ∏ k ∈ s.erase M, ((M : ℤ) - k) := by
  rw [eval_derivative_prod, sum_eq_single M]
  · intro i _ hi
    exact prod_eq_zero (i := M) (by simp; exact ⟨fun h => hi h.symm, hM⟩) (by simp)
  · intro h; exact absurd hM h

lemma eval_derivative_prod_log (s : Finset ℕ) (M : ℕ) (hM : M ∉ s) :
    (((derivative (∏ i ∈ s, (X - C (i : ℤ)))).eval (M : ℤ) : ℤ) : ℚ) =
      (∏ i ∈ s, ((M : ℚ) - i)) * ∑ i ∈ s, ((M : ℚ) - i)⁻¹ := by
  rw [eval_derivative_prod]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hne : (M : ℚ) - i ≠ 0 := by
    intro h; have : (M : ℚ) = i := by linarith
    have : M = i := by exact_mod_cast this
    exact hM (this ▸ hi)
  rw [← prod_erase_mul s (fun i : ℕ => ((M : ℚ) - i)) hi]
  field_simp

lemma harm_A (M : ℕ) : ∑ i ∈ range M, ((M : ℚ) - i)⁻¹ = harmonic M := by
  rw [← sum_range_reflect, harmonic]
  refine sum_congr rfl fun j hj => ?_
  simp at hj
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring_nf

lemma harm_B (n M : ℕ) (hM : M ≤ n) :
    ∑ i ∈ (range (n + 1)).erase M, ((M : ℚ) - i)⁻¹ = harmonic M - harmonic (n - M) := by
  rw [range_erase_eq n M hM, sum_union (disj_range_Ico M n), harm_A, sum_Ico_eq_sum_range,
    show n + 1 - (M + 1) = n - M by omega, sub_eq_add_neg]
  congr 1
  rw [harmonic, ← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  rw [show (M : ℚ) - (M + 1 + k) = -(k + 1) by ring, inv_neg]

lemma harm_C (n M : ℕ) (hM : M ≤ n) :
    ∑ i ∈ Icc (n + 1) (3 * n), ((M : ℚ) - i)⁻¹ = harmonic (n - M) - harmonic (3 * n - M) := by
  have hI : Icc (n + 1) (3 * n) = Ico (n + 1) (3 * n + 1) := rfl
  rw [hI, sum_Ico_eq_sum_range, show 3 * n + 1 - (n + 1) = 2 * n by omega,
    show 3 * n - M = (n - M) + 2 * n by omega, harmonic, harmonic, sum_range_add]
  rw [sub_add_cancel_left, ← sum_neg_distrib]
  refine sum_congr rfl fun k _ => ?_
  push_cast [Nat.cast_sub hM]
  rw [show (M : ℚ) - (n + 1 + k) = -(n - M + k + 1) by ring, inv_neg]


lemma delta_cast (n M : ℕ) :
    ∏ i ∈ (range (n + 1)).erase M, ((M : ℚ) - i) = (delta n M : ℚ) := by
  unfold delta; push_cast; rfl

lemma derivU_ne (n j M : ℕ) (hM : M ≤ n) (hj : j ≤ n) (hjM : j ≠ M) :
    (((derivative (polyU n j)).eval (M : ℤ) : ℤ) : ℚ) =
      (M.descFactorial j : ℚ) * (delta n M : ℚ) / ((M : ℚ) - j) := by
  have hq : (M : ℚ) - j ≠ 0 := by
    intro h; have : (M : ℚ) = j := by linarith
    exact hjM (by exact_mod_cast this.symm)
  have hMmem : M ∈ (range (n + 1)).erase j := by simp; omega
  have hjmem : j ∈ (range (n + 1)).erase M := by simp; omega
  unfold polyU
  rw [derivative_mul, eval_add, eval_mul, eval_mul, eval_prod_X_sub_C,
    prod_eq_zero (i := M) hMmem (by simp), mul_zero, zero_add,
    eval_derivative_prod_root _ _ hMmem, descPochhammer_eval_eq_descFactorial, delta,
    ← mul_prod_erase ((range (n + 1)).erase M) (fun i : ℕ => ((M : ℤ) - i)) hjmem,
    erase_right_comm]
  push_cast
  field_simp

lemma derivU_self (n M : ℕ) (hM : M ≤ n) :
    (((derivative (polyU n M)).eval (M : ℤ) : ℤ) : ℚ) =
      (M.factorial : ℚ) * (delta n M : ℚ) * (2 * harmonic M - harmonic (n - M)) := by
  unfold polyU
  rw [derivative_mul, eval_add, eval_mul, eval_mul, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_self, descPochhammer_eq_prod]
  push_cast
  rw [eval_derivative_prod_log _ _ (by simp), eval_derivative_prod_log _ _ (by simp), harm_A,
    harm_B n M hM, eval_prod_X_sub_C]
  have h1 : ∏ i ∈ range M, ((M : ℚ) - i) = M.factorial := by
    exact_mod_cast prod_range_sub M
  rw [h1, delta_cast]
  ring

/-- A4v: regularised values of `P` at the poles. -/
theorem polyP_value_at_node (n M : ℕ) (hM : M ≤ n) :
    (((polyP n).eval (M : ℤ) : ℤ) : ℚ) +
        ∑ j ∈ Finset.range M, (bInt n j : ℚ) * (M.descFactorial j : ℚ) / ((M : ℚ) - j) =
      -(M.factorial : ℚ) * (bInt n M : ℚ) * hcoef n M := by
  have hder := congrArg (fun p => (((derivative p).eval (M : ℤ) : ℤ) : ℚ))
    (polyN_eq_partialFraction n)
  simp only [derivative_add, derivative_mul, derivative_C, zero_mul, zero_add,
    derivative_sum, eval_add, eval_mul, eval_finsetSum, eval_C] at hder
  have hDM : (polyD n).eval (M : ℤ) = 0 := by
    unfold polyD; rw [eval_prod_X_sub_C]; exact prod_eq_zero (i := M) (by simp; omega) (by simp)
  have hD' : (derivative (polyD n)).eval (M : ℤ) = delta n M := by
    unfold polyD; rw [eval_derivative_prod_root _ _ (by simp; omega)]
  have hN : (((derivative (polyN n)).eval (M : ℤ) : ℤ) : ℚ) =
      (bInt n M : ℚ) * M.factorial * delta n M * (harmonic (n - M) - harmonic (3 * n - M)) := by
    unfold polyN
    rw [eval_derivative_prod_log _ _ (by simp; omega), harm_C n M hM]
    have := polyN_eval_node n M hM
    unfold polyN at this; rw [eval_prod_X_sub_C] at this
    have h2 : ∏ i ∈ Icc (n + 1) (3 * n), ((M : ℚ) - i) =
        (bInt n M : ℚ) * M.factorial * delta n M := by exact_mod_cast this
    rw [h2]
  rw [hDM, hD', mul_zero, zero_add] at hder
  push_cast at hder
  rw [delta_cast] at hder
  rw [hN, ← add_sum_erase _ _ (show M ∈ range (n + 1) by simp; omega), derivU_self n M hM] at hder
  have hsum : ∑ j ∈ (range (n + 1)).erase M,
      (bInt n j : ℚ) * (((derivative (polyU n j)).eval (M : ℤ) : ℤ) : ℚ) =
      (∑ j ∈ Finset.range M, (bInt n j : ℚ) * (M.descFactorial j : ℚ) / ((M : ℚ) - j)) *
        delta n M := by
    rw [sum_mul]
    symm
    apply sum_subset_zero_on_sdiff
    · intro j hj; simp at hj ⊢; omega
    · intro j hj
      simp at hj
      rw [derivU_ne n j M hM (by omega) (by omega),
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
      simp
    · intro j hj
      simp at hj
      rw [derivU_ne n j M hM (by omega) (by omega)]
      ring
  rw [hsum] at hder
  have hδ : (delta n M : ℚ) ≠ 0 := by exact_mod_cast delta_ne_zero n M hM
  apply mul_right_cancel₀ hδ
  unfold hcoef
  linear_combination (-1 : ℚ) * hder


/-- Newton coordinates: an integer polynomial of degree `≤ d` is an integer combination of
falling factorials `X^{(j)}`, `j ≤ d`. -/
lemma newton_expansion (d : ℕ) (P : ℤ[X]) (hP : P.natDegree ≤ d) :
    ∃ a : ℕ → ℤ, P = ∑ j ∈ range (d + 1), C (a j) * descPochhammer ℤ j := by
  induction d generalizing P with
  | zero =>
    refine ⟨fun _ => P.coeff 0, ?_⟩
    rw [sum_range_one, descPochhammer_zero, mul_one]
    exact eq_C_of_natDegree_le_zero hP
  | succ d ih =>
    set Q := P - C (P.coeff (d + 1)) * descPochhammer ℤ (d + 1) with hQ
    have hQd : Q.natDegree ≤ d := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      have hdeg : (descPochhammer ℤ (d + 1)).natDegree = d + 1 := descPochhammer_natDegree ℤ _
      rcases Nat.lt_or_ge (d + 1) N with h | h
      · rw [hQ, coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by omega),
          coeff_eq_zero_of_natDegree_lt (p := descPochhammer ℤ (d + 1)) (by omega)]
        simp
      · have hN' : N = d + 1 := by omega
        subst hN'
        have hm := (monic_descPochhammer ℤ (d + 1))
        rw [Monic, leadingCoeff, hdeg] at hm
        rw [hQ, coeff_sub, coeff_C_mul, hm]; simp
    obtain ⟨a, ha⟩ := ih Q hQd
    refine ⟨fun j => if j = d + 1 then P.coeff (d + 1) else a j, ?_⟩
    rw [sum_range_succ]
    dsimp only
    rw [if_pos rfl]
    have : ∑ j ∈ range (d + 1), C (if j = d + 1 then P.coeff (d + 1) else a j) *
        descPochhammer ℤ j = ∑ j ∈ range (d + 1), C (a j) * descPochhammer ℤ j := by
      refine sum_congr rfl fun j hj => ?_
      simp at hj; rw [if_neg (by omega)]
    rw [this, ← ha, hQ]; ring

lemma alt_inner (t : ℕ) :
    ∑ k ∈ range (t + 1), (-1 : ℚ) ^ k / ((k.factorial : ℚ) * ((t - k).factorial : ℚ)) =
      if t = 0 then 1 else 0 := by
  have h := Int.alternating_sum_range_choose (n := t)
  have h' : ∑ m ∈ range (t + 1), ((-1 : ℚ) ^ m * (t.choose m : ℚ)) = if t = 0 then 1 else 0 := by
    have := congrArg (Int.cast : ℤ → ℚ) h
    push_cast at this
    exact this
  have hf : (t.factorial : ℚ) ≠ 0 := by positivity
  have hc : ∀ k ∈ range (t + 1), (-1 : ℚ) ^ k / ((k.factorial : ℚ) * ((t - k).factorial : ℚ)) =
      ((-1 : ℚ) ^ k * (t.choose k : ℚ)) / (t.factorial : ℚ) := by
    intro k hk
    simp at hk
    rw [Nat.cast_choose ℚ (by omega)]
    field_simp
  rw [sum_congr rfl hc, ← sum_div, h']
  split_ifs with ht
  · subst ht; simp
  · simp

lemma expPartial_identity (s : ℕ) :
    ∑ k ∈ range (s + 1), (-1 : ℚ) ^ k / (k.factorial : ℚ) * expPartial (s - k) = 1 := by
  unfold expPartial
  have : ∑ k ∈ range (s + 1), (-1 : ℚ) ^ k / (k.factorial : ℚ) *
      ∑ l ∈ range (s - k + 1), ((l.factorial : ℚ))⁻¹ =
      ∑ k ∈ range (s + 1), ∑ l ∈ range (s + 1 - k),
        (-1 : ℚ) ^ k / ((k.factorial : ℚ) * (l.factorial : ℚ)) := by
    refine sum_congr rfl fun k hk => ?_
    simp at hk
    rw [mul_sum, show s + 1 - k = s - k + 1 by omega]
    refine sum_congr rfl fun l _ => ?_
    field_simp
  rw [this, ← sum_range_diag_flip (s + 1) (fun k l => (-1 : ℚ) ^ k / ((k.factorial : ℚ) * (l.factorial : ℚ)))]
  simp only [alt_inner]
  rw [sum_ite_eq' (range (s + 1)) 0]; simp

/-- `T_d(X^{(j)}) = (-1)^j` for `j ≤ d`. -/
lemma T_descPochhammer (d j : ℕ) (hj : j ≤ d) :
    ∑ i ∈ range (d + 1), (-1 : ℚ) ^ i * (i.descFactorial j : ℚ) / (i.factorial : ℚ) *
      expPartial (d - i) = (-1) ^ j := by
  rw [show d + 1 = j + (d - j + 1) by omega, sum_range_add]
  have h0 : ∑ i ∈ range j, (-1 : ℚ) ^ i * (i.descFactorial j : ℚ) / (i.factorial : ℚ) *
      expPartial (j + (d - j + 1) - 1 - i) = 0 := by
    refine sum_eq_zero fun i hi => ?_
    simp at hi
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hi]; simp
  have h0' : ∑ i ∈ range j, (-1 : ℚ) ^ i * (i.descFactorial j : ℚ) / (i.factorial : ℚ) *
      expPartial (d - i) = 0 := by
    refine sum_eq_zero fun i hi => ?_
    simp at hi
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hi]; simp
  rw [h0', zero_add]
  have hE := expPartial_identity (d - j)
  calc _ = (-1 : ℚ) ^ j * ∑ k ∈ range (d - j + 1),
        (-1 : ℚ) ^ k / (k.factorial : ℚ) * expPartial (d - j - k) := ?_
    _ = (-1) ^ j := by rw [hE, mul_one]
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  simp at hk
  have hfd := Nat.factorial_mul_descFactorial (n := j + k) (k := j) (by omega)
  rw [show j + k - j = k by omega] at hfd
  have hkf : (k.factorial : ℚ) ≠ 0 := by positivity
  have hdf : ((j + k).descFactorial j : ℚ) = ((j + k).factorial : ℚ) / (k.factorial : ℚ) := by
    rw [← hfd]; push_cast; field_simp
  rw [show d - (j + k) = d - j - k by omega, pow_add, hdf]
  field_simp


lemma neg_one_pow_sq (m : ℕ) : (-1 : ℚ) ^ m * (-1) ^ m = 1 := by
  rw [← mul_pow]; norm_num

/-- `P(i)/i! = -(-1)^(n-i) c_i`, where `c_i` is the `i`-th bracket in `pCoef`. -/
lemma node_c (n i : ℕ) (hi : i ≤ n) :
    (((polyP n).eval (i : ℤ) : ℤ) : ℚ) / (i.factorial : ℚ) =
      -(-1) ^ (n - i) * (beta n i * hcoef n i +
        ∑ k ∈ range i, (-1 : ℚ) ^ (i - k) * beta n k /
          (((i - k : ℕ) : ℚ) * ((i - k).factorial : ℚ))) := by
  have hA := polyP_value_at_node n i hi
  have hf : (i.factorial : ℚ) ≠ 0 := by positivity
  have hsum : ∑ k ∈ range i, (bInt n k : ℚ) * (i.descFactorial k : ℚ) / ((i : ℚ) - k) =
      (-1) ^ (n - i) * (i.factorial : ℚ) * ∑ k ∈ range i, (-1 : ℚ) ^ (i - k) * beta n k /
          (((i - k : ℕ) : ℚ) * ((i - k).factorial : ℚ)) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    simp at hk
    rw [bInt_cast n k (by omega), show n - k = (n - i) + (i - k) by omega, pow_add]
    have hfd := Nat.factorial_mul_descFactorial (n := i) (k := k) (by omega)
    have hdf : (i.descFactorial k : ℚ) = (i.factorial : ℚ) / ((i - k).factorial : ℚ) := by
      rw [← hfd]; push_cast; field_simp
    have hik : ((i - k : ℕ) : ℚ) = (i : ℚ) - k := by push_cast [Nat.cast_sub (by omega : k ≤ i)]; ring
    have hne : (i : ℚ) - k ≠ 0 := by
      have : (k : ℚ) < i := by exact_mod_cast hk
      linarith
    rw [hdf, hik]
    field_simp
  rw [hsum, bInt_cast n i hi] at hA
  rw [div_eq_iff hf]
  linear_combination hA

/-- A1 + A5: Newton coordinates of `P_n` and the constant term. -/
theorem polyP_newton (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : ℕ → ℤ,
      polyP n = ∑ j ∈ Finset.range n, Polynomial.C (a j) * descPochhammer ℤ j ∧
      (∀ M : ℕ, (((polyP n).eval (M : ℤ) : ℤ) : ℚ) =
        ∑ j ∈ Finset.range n, (a j : ℚ) * (M.descFactorial j : ℚ)) ∧
      ((∑ j ∈ Finset.range n, (-1 : ℤ) ^ j * a j : ℤ) : ℚ) = (-1) ^ (n + 1) * pCoef n := by
  obtain ⟨a, ha⟩ := newton_expansion (n - 1) (polyP n)
    (by have := polyP_natDegree_lt n hn; omega)
  rw [show n - 1 + 1 = n by omega] at ha
  have hval : ∀ M : ℕ, (((polyP n).eval (M : ℤ) : ℤ) : ℚ) =
      ∑ j ∈ Finset.range n, (a j : ℚ) * (M.descFactorial j : ℚ) := by
    intro M
    rw [ha, eval_finsetSum]
    push_cast
    refine sum_congr rfl fun j _ => ?_
    rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial]; push_cast; ring
  refine ⟨a, ha, hval, ?_⟩
  have hp : pCoef n = (-1) ^ (n + 1) * ∑ i ∈ range n, (-1 : ℚ) ^ i *
      ((((polyP n).eval (i : ℤ) : ℤ) : ℚ) / (i.factorial : ℚ)) * expPartial (n - 1 - i) := by
    unfold pCoef
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    simp at hi
    rw [node_c n i (by omega)]
    have hs : (-1 : ℚ) ^ (n + 1) * (-1) ^ i * (-1) ^ (n - i) = -1 := by
      rw [← pow_add, ← pow_add, show n + 1 + i + (n - i) = 2 * n + 1 by omega, pow_succ, pow_mul]
      norm_num
    linear_combination ((beta n i * hcoef n i + ∑ k ∈ range i, (-1 : ℚ) ^ (i - k) * beta n k /
          (((i - k : ℕ) : ℚ) * ((i - k).factorial : ℚ))) * expPartial (n - 1 - i)) * hs
  have hT : ∑ i ∈ range n, (-1 : ℚ) ^ i *
      ((((polyP n).eval (i : ℤ) : ℤ) : ℚ) / (i.factorial : ℚ)) * expPartial (n - 1 - i) =
      ∑ j ∈ range n, (-1 : ℚ) ^ j * (a j : ℚ) := by
    calc _ = ∑ i ∈ range n, ∑ j ∈ range n, (a j : ℚ) * ((-1 : ℚ) ^ i *
          (i.descFactorial j : ℚ) / (i.factorial : ℚ) * expPartial (n - 1 - i)) := by
          refine sum_congr rfl fun i _ => ?_
          rw [hval, sum_div, mul_sum, sum_mul]
          refine sum_congr rfl fun j _ => ?_
          ring
      _ = ∑ j ∈ range n, (a j : ℚ) * ∑ i ∈ range n, ((-1 : ℚ) ^ i *
          (i.descFactorial j : ℚ) / (i.factorial : ℚ) * expPartial (n - 1 - i)) := by
          rw [sum_comm]
          refine sum_congr rfl fun j _ => ?_
          rw [mul_sum]
      _ = _ := by
          refine sum_congr rfl fun j hj => ?_
          simp at hj
          have := T_descPochhammer (n - 1) j (by omega)
          rw [show n - 1 + 1 = n by omega] at this
          rw [this]; ring
  rw [hp, hT]
  push_cast
  rw [← mul_assoc, neg_one_pow_sq, one_mul]

end EulerMascheroni.Rivoal.PolyAux

theorem solution (n j : ℕ) (hj : j ≤ n) :
    (EulerMascheroni.Rivoal.bInt n j : ℚ) = (-1) ^ (n - j) * EulerMascheroni.Rivoal.beta n j :=
  EulerMascheroni.Rivoal.PolyAux.bInt_cast n j hj
