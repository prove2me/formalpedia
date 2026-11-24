-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.shannon_joint_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:18.793314+00:00
-- url     : https://prove2.me/submissions/148ccbc4-7e57-4947-80df-fea73ccbad6f

module
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_divergence_nonneg

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]
namespace BalanceSpecification.FiniteEntropy
theorem _root_.solution {κ : Type*} [Fintype κ] {p : ι × κ → ℝ}
    (hp : ∀ ij, 0 ≤ p ij) (hsum : ∑ ij, p ij = 1) :
    shannon p ≤ shannon (fun i => ∑ j, p (i, j)) +
      shannon (fun j => ∑ i, p (i, j)) := by
  let r : ι → ℝ := fun i => ∑ j, p (i, j)
  let s : κ → ℝ := fun j => ∑ i, p (i, j)
  have hr i : 0 ≤ r i := Finset.sum_nonneg (fun j _ => hp (i, j))
  have hs j : 0 ≤ s j := Finset.sum_nonneg (fun i _ => hp (i, j))
  have hrows : ∑ i, r i = 1 := by
    simpa only [r, Fintype.sum_prod_type] using hsum
  have hcols : ∑ j, s j = 1 := by
    simp only [s]
    rw [Finset.sum_comm]
    exact hrows
  let q : ι × κ → ℝ := fun ij => r ij.1 * s ij.2
  have hqsum : ∑ ij, q ij = 1 := by
    simp only [q, Fintype.sum_prod_type, ← Finset.mul_sum, hcols, mul_one, hrows]
  have hpositive ij (hne : p ij ≠ 0) : 0 < r ij.1 ∧ 0 < s ij.2 := by
    have hpp : 0 < p ij := lt_of_le_of_ne (hp ij) (Ne.symm hne)
    constructor
    · exact hpp.trans_le (Finset.single_le_sum (fun j _ => hp (ij.1, j))
        (Finset.mem_univ ij.2))
    · exact hpp.trans_le (Finset.single_le_sum (fun i _ => hp (i, ij.2))
        (Finset.mem_univ ij.1))
  have hD := divergence_nonneg hp (fun ij => mul_nonneg (hr ij.1) (hs ij.2))
    hsum hqsum (fun ij hne => mul_pos (hpositive ij hne).1 (hpositive ij hne).2)
  have hexpansion ij : p ij * Real.log (p ij / q ij) =
      p ij * Real.log (p ij) - p ij * Real.log (r ij.1) -
        p ij * Real.log (s ij.2) := by
    by_cases hz : p ij = 0
    · simp only [hz, zero_mul, sub_self]
    · obtain ⟨hrp, hsp⟩ := hpositive ij hz
      dsimp only [q]
      rw [Real.log_div hz (mul_pos hrp hsp).ne', Real.log_mul hrp.ne' hsp.ne']
      ring
  have hcrossr : ∑ ij, p ij * Real.log (r ij.1) = ∑ i, r i * Real.log (r i) := by
    simp only [Fintype.sum_prod_type, ← Finset.sum_mul, r]
  have hcrosss : ∑ ij, p ij * Real.log (s ij.2) = ∑ j, s j * Real.log (s j) := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, s]
  have hformula : divergence p q = -shannon p + shannon r + shannon s := by
    rw [divergence, Finset.sum_congr rfl (fun ij _ => hexpansion ij)]
    simp only [Finset.sum_sub_distrib, hcrossr, hcrosss,
      shannon, neg_mul, Finset.sum_neg_distrib]
    ring
  rw [hformula] at hD
  change shannon p ≤ shannon r + shannon s
  linarith only [hD]
end BalanceSpecification.FiniteEntropy
