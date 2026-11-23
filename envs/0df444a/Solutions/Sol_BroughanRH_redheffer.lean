-- Prove2me | solution 1 for BroughanRH.redheffer
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:43:56.828916+00:00
-- url     : https://prove2.me/submissions/a617c219-b9fc-45a6-a824-766eadfda368
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Mathlib

open Finset ArithmeticFunction Matrix
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace BRHRed

/-- Mertens function (real-valued). -/
noncomputable def M (y : ℕ) : ℝ := ∑ b ∈ Ioc 0 y, ((μ b : ℤ) : ℝ)

/-- `∑_{k ≤ z} M(z / k) = 1` for `z ≥ 1`. -/
lemma sum_M_div (z : ℕ) (hz : 1 ≤ z) : ∑ k ∈ Ioc 0 z, M (z / k) = 1 := by
  have h := sum_Ioc_mul_eq_sum_sum ((ζ : ArithmeticFunction ℤ)) μ z
  rw [coe_zeta_mul_moebius] at h
  have h1 : ∑ n ∈ Ioc 0 z, (1 : ArithmeticFunction ℤ) n = 1 := by
    simp only [ArithmeticFunction.one_apply]
    rw [sum_ite_eq']
    simp [mem_Ioc]; omega
  rw [h1] at h
  have h2 : ∑ k ∈ Ioc 0 z, M (z / k) = ((∑ n ∈ Ioc 0 z, (ζ : ArithmeticFunction ℤ) n * ∑ m ∈ Ioc 0 (z / n), μ m : ℤ) : ℝ) := by
    push_cast
    refine sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := (mem_Ioc.1 hk).1.ne'
    simp [M, natCoe_apply, zeta_apply, hk0]
  rw [h2, ← h]; simp

lemma sum_dvd (d y : ℕ) (hd : 0 < d) (f : ℕ → ℝ) :
    ∑ m ∈ Ioc 0 y, (if d ∣ m then f (y / m) else 0) = ∑ k ∈ Ioc 0 (y / d), f (y / d / k) := by
  rw [← sum_filter]
  have : (Ioc 0 y).filter (fun m => d ∣ m) = (Ioc 0 (y / d)).image (fun k => d * k) := by
    ext m
    simp only [mem_filter, mem_Ioc, mem_image]
    constructor
    · rintro ⟨⟨h0, hy⟩, k, rfl⟩
      refine ⟨k, ⟨Nat.pos_of_mul_pos_left h0, ?_⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le hd]; linarith [mul_comm d k]
    · rintro ⟨k, ⟨hk0, hk⟩, rfl⟩
      rw [Nat.le_div_iff_mul_le hd] at hk
      exact ⟨⟨Nat.mul_pos hd hk0, by linarith [mul_comm d k]⟩, dvd_mul_right d k⟩
  rw [this, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd h)]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.div_div_eq_div_mul]

lemma sum_range_shift (n : ℕ) (f : ℕ → ℝ) : ∑ j ∈ range n, f (j + 1) = ∑ m ∈ Ioc 0 n, f m := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih, sum_Ioc_succ_top (Nat.zero_le n)]

noncomputable def U (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if (i.val + 1) ∣ (j.val + 1) then 1 else 0

lemma det_U (n : ℕ) : (U n).det = 1 := by
  rw [det_of_isUpperTriangular]
  · simp [U]
  · intro i j hij
    simp only [U]
    rw [if_neg]
    intro h
    have := Nat.le_of_dvd (Nat.succ_pos _) h
    have : (j : ℕ) < i := hij
    omega

noncomputable def x (n : ℕ) : Fin n → ℝ := fun j => M (n / (j.val + 1))

lemma U_mulVec_x (n : ℕ) : U n *ᵥ x n = fun _ => 1 := by
  funext i
  simp only [mulVec, dotProduct, U, x, ite_mul, one_mul, zero_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j => if (i.val + 1) ∣ (j + 1) then M (n / (j + 1)) else 0) n,
    sum_range_shift n (fun m => if (i.val + 1) ∣ m then M (n / m) else 0),
    sum_dvd (i.val + 1) n (Nat.succ_pos _) M]
  apply sum_M_div
  rw [Nat.le_div_iff_mul_le (Nat.succ_pos _)]
  have := i.isLt; omega

lemma redheffer_det (n : ℕ) (hn : 0 < n) :
    (Matrix.of fun i j : Fin n => if j.val = 0 ∨ (i.val + 1) ∣ (j.val + 1) then (1 : ℝ) else 0).det
      = M n := by
  have hA : (Matrix.of fun i j : Fin n => if j.val = 0 ∨ (i.val + 1) ∣ (j.val + 1) then (1 : ℝ) else 0)
      = (U n).updateCol ⟨0, hn⟩ (fun _ => 1) := by
    ext i j
    simp only [of_apply, updateCol_apply, U]
    by_cases hj : j = ⟨0, hn⟩
    · subst hj; simp
    · have : j.val ≠ 0 := fun h => hj (Fin.ext h)
      simp [hj, this]
  rw [hA, ← cramer_apply, ← U_mulVec_x, cramer_eq_adjugate_mulVec, mulVec_mulVec, adjugate_mul,
    det_U, one_smul, one_mulVec]
  simp [x]

end BRHRed

open BRHRed in
theorem solution :
    let A (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => if j.val = 0 ∨ (i.val + 1) ∣ (j.val + 1) then 1 else 0
    ∀ ε : ℝ, 0 < ε → Asymptotics.IsBigO Filter.atTop (fun n => (A n).det) (fun n : ℕ => (n : ℝ) ^ (1/2 + ε)) := by
  intro A ε hε
  have hM := moebius_summatory_rpow_bound_of_riemannHypothesis riemann_hypothesis ε hε
  refine Asymptotics.IsBigO.trans ?_ hM
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hdet : (A n).det = M n := redheffer_det n hn
  have hc : (((M n : ℝ)) : ℂ) = ∑ k ∈ Finset.Icc 1 n, ((μ k : ℤ) : ℂ) := by
    have : Finset.Icc 1 n = Ioc 0 n := by ext; simp only [mem_Icc, mem_Ioc]; omega
    rw [this, M]; push_cast; rfl
  rw [hdet, one_mul, ← hc, Complex.norm_real]
