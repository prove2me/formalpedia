-- Prove2me | solution 1 for CovariateSAA.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T07:23:38.171143+00:00
-- url     : https://prove2.me/submissions/7b00ee37-f1d5-4ff4-974a-1d2c0d673aae

import Mathlib
import Definitions.Def_CovariateSAA_Setting

namespace Aux_CovSAA3

lemma core {n : ℕ} (A B C : Fin n → ℝ) (hB : ∀ i, 0 ≤ B i) (hC : ∀ i, 0 ≤ C i)
    (hA0 : ∀ i, 0 ≤ A i) (hABC : ∀ i, A i ≤ B i + C i) :
    Real.sqrt (∑ i, A i ^ 2) ≤ Real.sqrt (∑ i, B i ^ 2) + Real.sqrt (∑ i, C i ^ 2) := by
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have h1 : ∑ i, A i ^ 2 ≤ ∑ i, (B i + C i) ^ 2 :=
    Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (hA0 i) (hABC i) 2)
  have h2 : ∑ i, (B i + C i) ^ 2 = ∑ i, B i ^ 2 + 2 * ∑ i, B i * C i + ∑ i, C i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h3 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ B C
  have hb := Real.sq_sqrt (Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (B i)))
  have hc := Real.sq_sqrt (Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (C i)))
  nlinarith

end Aux_CovSAA3

open CovariateSAA Aux_CovSAA3 in
theorem solution {dx dy : ℕ} {Ω : Type*} (D : Data dx dy Ω) (n : ℕ) (ω : Ω) :
    Real.sqrt (empMean n (fun i => ‖Ring.inverse (D.Qhat n ω (D.xs i ω))‖ ^ 2)) ≤
      Real.sqrt (empMean n (fun i =>
        ‖Ring.inverse (D.Qhat n ω (D.xs i ω)) - Ring.inverse (D.Qstar (D.xs i ω))‖ ^ 2)) +
      Real.sqrt (empMean n (fun i => ‖Ring.inverse (D.Qstar (D.xs i ω))‖ ^ 2)) := by
  unfold empMean
  have hn : (0:ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  rw [Real.sqrt_mul hn, Real.sqrt_mul hn, Real.sqrt_mul hn, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply core
  · intro i; exact norm_nonneg _
  · intro i; exact norm_nonneg _
  · intro i; exact norm_nonneg _
  · intro i
    have := norm_add_le (Ring.inverse (D.Qhat n ω (D.xs i ω)) - Ring.inverse (D.Qstar (D.xs i ω)))
      (Ring.inverse (D.Qstar (D.xs i ω)))
    rwa [sub_add_cancel] at this
