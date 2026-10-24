-- Prove2me | solution 1 for BellDetEff.TwoParty.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:22:43.127073+00:00
-- url     : https://prove2.me/submissions/0999f8ca-63f9-45ba-b55f-8ee45e180933

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_Efficiency
import Definitions.Def_BellDetEff_TwoParty_BellInequality
import Theorems.Thm_BellDetEff_TwoParty_eqs_13_14_witness

namespace BellDetEff.TwoParty.EvaluationProof

lemma sum_four_swap {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    (f : A → B → X → Y → ℝ) :
    (∑ a, ∑ b, ∑ x, ∑ y, f a b x y) = ∑ x, ∑ y, ∑ a, ∑ b, f a b x y := by
  calc
    _ = ∑ a, ∑ x, ∑ b, ∑ y, f a b x y := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ x, ∑ a, ∑ b, ∑ y, f a b x y := Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ a, ∑ b, f a b x y := by
      apply Finset.sum_congr rfl
      intro x _
      calc
        _ = ∑ a, ∑ y, ∑ b, f a b x y := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

lemma sum_bellG (MA : ℕ) (hA : 1 ≤ MA) : ∑ x : Fin MA, bellG x = 1 - (MA : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : MA ≠ 0)
  simp [Fin.sum_univ_succ, bellG]

lemma sum_bellH (MB : ℕ) (hB : 1 ≤ MB) : ∑ y : Fin MB, bellH y = 1 - (MB : ℝ) := by
  simpa only [bellG, bellH] using sum_bellG MB hB

lemma input_count (MA MB : ℕ) (hA : 1 ≤ MA) (hB : 1 ≤ MB) :
    (∑ x : Fin MA, ∑ y : Fin MB, if x.val = 0 ∧ y.val = 0 then (0 : ℝ) else 1) =
      (MA : ℝ) * MB - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : MA ≠ 0)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : MB ≠ 0)
  simp [Fin.sum_univ_succ]
  ring

lemma joint_block (P MA MB : ℕ) [Fact P.Prime] (x : Fin MA) (y : Fin MB) :
    (∑ a, ∑ b, bellF P a b x y * witnessBox P MA MB a b x y) =
      if x.val = 0 ∧ y.val = 0 then 0 else 1 := by
  have hprob := (eqs_13_14_witness P MA MB).1.2 x y
  have hpoint (a b : Fin P) : bellF P a b x y * witnessBox P MA MB a b x y =
      (if x.val = 0 ∧ y.val = 0 then 0 else 1) * witnessBox P MA MB a b x y := by
    by_cases hc : bellCong P a b x y
    · by_cases hx : x.val = 0 <;> by_cases hy : y.val = 0 <;>
        simp [bellF, witnessBox, hc, hx, hy]
    · simp [bellF, witnessBox, hc]
  simp_rw [hpoint, ← Finset.mul_sum]
  rw [hprob, mul_one]

lemma marginalA_eff (P MA MB : ℕ) [Fact P.Prime] (hB : 1 ≤ MB) (η : ℝ)
    (a : Fin P) (x : Fin MA) :
    marginalA (withEff (witnessBox P MA MB) η) (some a) x = η / P := by
  have hrow := (eqs_13_14_witness P MA MB).2.2.1
  have hy (y : Fin MB) :
      ∑ b, withEff (witnessBox P MA MB) η (some a) b x y = η / P := by
    rw [Fintype.sum_option]
    simp only [withEff, ← Finset.mul_sum, hrow]
    ring
  simp only [marginalA, hy, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hb : (MB : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

lemma marginalB_eff (P MA MB : ℕ) [Fact P.Prime] (hA : 1 ≤ MA) (η : ℝ)
    (b : Fin P) (y : Fin MB) :
    marginalB (withEff (witnessBox P MA MB) η) (some b) y = η / P := by
  have hcol := (eqs_13_14_witness P MA MB).2.2.2
  have hx (x : Fin MA) :
      ∑ a, withEff (witnessBox P MA MB) η a (some b) x y = η / P := by
    rw [Fintype.sum_option]
    simp only [withEff, ← Finset.mul_sum, hcol]
    ring
  simp only [marginalB, hx, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have ha : (MA : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

lemma joint_total (P MA MB : ℕ) [Fact P.Prime] (hA : 1 ≤ MA) (hB : 1 ≤ MB) (η : ℝ) :
    (∑ a : Fin P, ∑ b : Fin P, ∑ x : Fin MA, ∑ y : Fin MB,
      bellF P a b x y * withEff (witnessBox P MA MB) η (some a) (some b) x y) =
        η ^ 2 * ((MA : ℝ) * MB - 1) := by
  have hs (a b : Fin P) (x : Fin MA) (y : Fin MB) :
      bellF P a b x y * withEff (witnessBox P MA MB) η (some a) (some b) x y =
        η ^ 2 * (bellF P a b x y * witnessBox P MA MB a b x y) := by
    simp only [withEff]
    ring
  simp_rw [hs, ← Finset.mul_sum]
  rw [sum_four_swap]
  simp_rw [joint_block]
  rw [input_count MA MB hA hB]

end BellDetEff.TwoParty.EvaluationProof

open BellDetEff.TwoParty BellDetEff.TwoParty.EvaluationProof

theorem solution (P MA MB : ℕ) [Fact P.Prime] (hA : 1 ≤ MA) (hB : 1 ≤ MB) (_hAP : MA ≤ P)
    (_hBP : MB ≤ P) (η : ℝ) :
    bellValue P (withEff (witnessBox P MA MB) η) =
      η ^ 2 * ((MA : ℝ) * MB - 1) - η * ((MA : ℝ) + MB - 2) := by
  have hP : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : P.Prime).ne_zero
  unfold bellValue
  rw [joint_total P MA MB hA hB η]
  simp_rw [marginalA_eff P MA MB hB η, marginalB_eff P MA MB hA η, ← Finset.sum_mul]
  rw [sum_bellG MA hA, sum_bellH MB hB]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring
