-- Prove2me | solution 1 for DNFSatMQ.Main.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T16:35:03.880319+00:00
-- url     : https://prove2.me/submissions/e7d88266-585e-4a56-8faf-8a4d785f3f58

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Basic

namespace DNFSatMQ.Main

theorem unif_toReal {α : Type} [DecidableEq α] (A : Finset α) (hA : A.Nonempty) (x : α) :
    ((PMF.uniformOfFinset A hA) x).toReal = if x ∈ A then 1 / (A.card : ℝ) else 0 := by
  rw [PMF.uniformOfFinset_apply]
  split_ifs
  · simp
  · simp

theorem sum_ite_const {α : Type} [Fintype α] [DecidableEq α] (A : Finset α) (r : ℝ) :
    (∑ x, if x ∈ A then r else 0) = A.card * r := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

end DNFSatMQ.Main

open DNFSatMQ.Main

theorem solution {α : Type} [Fintype α] [DecidableEq α] (A B : Finset α) (hA : A.Nonempty)
    (hB : B.Nonempty) :
    SSNonExt.TV (PMF.uniformOfFinset A hA) (PMF.uniformOfFinset B hB) =
        1 - ((A ∩ B).card : ℝ) / (max A.card B.card : ℕ) ∧
      1 - ((A ∩ B).card : ℝ) / (max A.card B.card : ℕ) ≤ (((A \ B) ∪ (B \ A)).card : ℝ) / A.card := by
  have ha : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  set a : ℝ := (A.card : ℝ) with ha_def
  set b : ℝ := (B.card : ℝ) with hb_def
  set c : ℝ := ((A ∩ B).card : ℝ) with hc_def
  have hmcast : ((max A.card B.card : ℕ) : ℝ) = max a b := by
    rw [Nat.cast_max]
  rw [hmcast]
  have hm : 0 < max a b := lt_max_of_lt_left ha
  have hca : c ≤ a := by
    rw [hc_def, ha_def]; exact_mod_cast Finset.card_le_card Finset.inter_subset_left
  have hcb : c ≤ b := by
    rw [hc_def, hb_def]; exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  constructor
  · unfold SSNonExt.TV IsingLTL.BeliefProp.tvDist
    beta_reduce
    have key : ∀ x : α, |(if x ∈ A then 1 / a else 0) - (if x ∈ B then 1 / b else 0)| =
        (if x ∈ A then 1 / a else 0) + (if x ∈ B then 1 / b else 0)
          - 2 * (if x ∈ A ∩ B then 1 / max a b else 0) := by
      intro x
      by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> simp only [hxA, hxB, Finset.mem_inter,
        and_true, and_false, true_and, false_and, if_true, if_false]
      · rcases le_total a b with hab | hab
        · rw [max_eq_right hab]
          have : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hab
          rw [abs_of_nonneg (by linarith)]; ring
        · rw [max_eq_left hab]
          have : 1 / a ≤ 1 / b := one_div_le_one_div_of_le hb hab
          rw [abs_of_nonpos (by linarith)]; ring
      · have : 0 < 1 / a := div_pos one_pos ha
        rw [abs_of_nonneg (by linarith)]; ring
      · have : 0 < 1 / b := div_pos one_pos hb
        rw [abs_of_nonpos (by linarith)]; ring
      · norm_num
    have hs : (∑ x : α, |((PMF.uniformOfFinset A hA) x).toReal
        - ((PMF.uniformOfFinset B hB) x).toReal|) =
        ∑ x : α, ((if x ∈ A then 1 / a else 0) + (if x ∈ B then 1 / b else 0)
          - 2 * (if x ∈ A ∩ B then 1 / max a b else 0)) :=
      Finset.sum_congr rfl (fun x _ => by rw [unif_toReal, unif_toReal]; exact key x)
    rw [hs]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_ite_const,
      sum_ite_const, sum_ite_const]
    rw [← ha_def, ← hb_def, ← hc_def]
    field_simp
    ring
  · have hsymm : (((A \ B) ∪ (B \ A)).card : ℝ) = a + b - 2 * c := by
      have h1 : ((A \ B) ∪ (B \ A)).card = (A \ B).card + (B \ A).card :=
        Finset.card_union_of_disjoint disjoint_sdiff_sdiff
      have h2 : (A \ B).card + (A ∩ B).card = A.card := Finset.card_sdiff_add_card_inter A B
      have h3 : (B \ A).card + (B ∩ A).card = B.card := Finset.card_sdiff_add_card_inter B A
      rw [Finset.inter_comm] at h3
      rw [h1, hc_def, ha_def, hb_def]
      have h2' : ((A \ B).card : ℝ) + (A ∩ B).card = A.card := by exact_mod_cast h2
      have h3' : ((B \ A).card : ℝ) + (A ∩ B).card = B.card := by exact_mod_cast h3
      push_cast
      linarith
    rw [hsymm]
    rcases le_total a b with hab | hab
    · have e : 1 - c / b = (b - c) / b := by field_simp
      rw [max_eq_right hab, e, div_le_div_iff₀ hb ha]
      nlinarith
    · have e : 1 - c / a = (a - c) / a := by field_simp
      rw [max_eq_left hab, e, div_le_div_iff₀ ha ha]
      nlinarith
