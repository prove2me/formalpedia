-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.shannon_le_log_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:27.302943+00:00
-- url     : https://prove2.me/submissions/ab78a76d-da87-4a57-b0b1-a6b290618523

module
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_divergence_nonneg
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_divergence_eq_neg_shannon_sub


set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]
namespace BalanceSpecification.FiniteEntropy
theorem _root_.solution {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) : shannon p ≤ Real.log (Fintype.card ι) := by
  have hne : Nonempty ι := by
    by_contra h
    have hzero : ∑ i, p i = 0 := Finset.sum_eq_zero (by
      intro i _
      exact (h ⟨i⟩).elim)
    linarith only [hzero, hpsum]
  let := hne
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  let q : ι → ℝ := fun _ => 1 / Fintype.card ι
  have hqpos i : 0 < q i := div_pos zero_lt_one hcard
  have hqsum : ∑ i, q i = 1 := by
    simp only [q, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel hcard.ne'
  have hD := divergence_nonneg hp (fun i => (hqpos i).le) hpsum hqsum
    (fun i _ => hqpos i)
  rw [divergence_eq_neg_shannon_sub hqpos] at hD
  have hcross : ∑ i, p i * Real.log (q i) = -Real.log (Fintype.card ι) := by
    simp only [q, one_div, Real.log_inv, ← Finset.sum_mul, hpsum, one_mul]
  rw [hcross] at hD
  linarith only [hD]
end BalanceSpecification.FiniteEntropy
