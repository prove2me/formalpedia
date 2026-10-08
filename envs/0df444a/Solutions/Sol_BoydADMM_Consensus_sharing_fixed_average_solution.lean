-- Prove2me | solution 1 for BoydADMM.Consensus.sharing_fixed_average_solution
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:25:27.757507+00:00
-- url     : https://prove2.me/submissions/0a7204dc-56d6-47d0-8639-e0b823537fc3

import Definitions.Def_BoydADMM_Consensus_Model


open scoped BigOperators InnerProductSpace
open BoydADMM.Consensus

namespace NProof

lemma avg_add {n N : ℕ} (a b : Fin N → EuclideanSpace ℝ (Fin n)) :
    avg (fun i => a i + b i) = avg a + avg b := by
  simp [avg, Finset.sum_add_distrib, smul_add]

lemma avg_sub {n N : ℕ} (a b : Fin N → EuclideanSpace ℝ (Fin n)) :
    avg (fun i => a i - b i) = avg a - avg b := by
  simp [avg, Finset.sum_sub_distrib, smul_sub]

lemma avg_smul {n N : ℕ} (r : ℝ) (a : Fin N → EuclideanSpace ℝ (Fin n)) :
    avg (fun i => r • a i) = r • avg a := by
  simp [avg, ← Finset.smul_sum, smul_smul, mul_comm]

lemma avg_const {n N : ℕ} (hN : 0 < N) (w : EuclideanSpace ℝ (Fin n)) :
    avg (fun _ : Fin N => w) = w := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp [avg, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hN0]

lemma sum_eq_smul_avg {n N : ℕ} (hN : 0 < N)
    (a : Fin N → EuclideanSpace ℝ (Fin n)) :
    ∑ i, a i = (N : ℝ) • avg a := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp [avg, smul_smul, hN0]

lemma lift_avg {n N : ℕ} (hN : 0 < N)
    (a : Fin N → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n)) :
    avg (fun i => a i + w - avg a) = w := by
  rw [avg_sub, avg_add, avg_const hN, avg_const hN]
  abel

lemma variance {n N : ℕ} (hN : 0 < N)
    (a z : Fin N → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n))
    (hz : avg z = w) :
    ∑ i, ‖z i - a i‖ ^ 2 =
      (∑ i, ‖z i - (a i + w - avg a)‖ ^ 2) + ∑ _i : Fin N, ‖w - avg a‖ ^ 2 := by
  have hsum : ∑ i, (z i - (a i + w - avg a)) = 0 := by
    rw [sum_eq_smul_avg hN, avg_sub, hz, lift_avg hN, sub_self, smul_zero]
  have hi (i : Fin N) : z i - a i = (z i - (a i + w - avg a)) + (w - avg a) := by abel
  simp_rw [hi, norm_add_sq_real]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← sum_inner, hsum, inner_zero_left,
    mul_zero, add_zero]

lemma fixed_average {n N : ℕ} (hN : 0 < N)
    (a z : Fin N → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n)) :
    (avg z = w ∧ ∀ z' : Fin N → EuclideanSpace ℝ (Fin n), avg z' = w →
        ∑ i, ‖z i - a i‖ ^ 2 ≤ ∑ i, ‖z' i - a i‖ ^ 2) ↔
      ∀ i, z i = a i + w - avg a := by
  constructor
  · rintro ⟨hz, hm⟩
    have h := hm (fun i => a i + w - avg a) (lift_avg hN a w)
    have hc (i : Fin N) : a i + w - avg a - a i = w - avg a := by abel
    simp_rw [hc] at h
    rw [variance hN a z w hz] at h
    have hs : ∑ i, ‖z i - (a i + w - avg a)‖ ^ 2 = 0 :=
      le_antisymm (by linarith) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg
      ‖z j - (a j + w - avg a)‖)).mp hs i (Finset.mem_univ i)
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hi))
  · intro hz
    have he : z = (fun i => a i + w - avg a) := funext hz
    constructor
    · rw [he]; exact lift_avg hN a w
    · intro z' hz'
      rw [variance hN a z' w hz', he]
      have hc (i : Fin N) : a i + w - avg a - a i = w - avg a := by abel
      simp_rw [hc]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => sq_nonneg _)

end NProof


/-- (7.13), §7.3, p. 57: with the average `z̄ = w` fixed, the problem of minimizing
`∑_i ‖z_i − a_i‖²` over `(z_1, …, z_N)` subject to `(1/N)∑_i z_i = w` has the unique solution
`z_i = a_i + w − ā`. (With `z̄` fixed, the term `g(N z̄)` of the book's objective is constant and
the factor `ρ/2 > 0` does not change the minimizers.) -/
theorem solution {n N : ℕ} (hN : 0 < N)
    (a z : Fin N → EuclideanSpace ℝ (Fin n)) (w : EuclideanSpace ℝ (Fin n)) :
    (avg z = w ∧ ∀ z' : Fin N → EuclideanSpace ℝ (Fin n), avg z' = w →
        ∑ i, ‖z i - a i‖ ^ 2 ≤ ∑ i, ‖z' i - a i‖ ^ 2) ↔
      ∀ i, z i = a i + w - avg a := by
  exact @NProof.fixed_average n N hN a z w

