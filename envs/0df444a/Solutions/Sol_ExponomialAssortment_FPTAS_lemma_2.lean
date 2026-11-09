-- Prove2me | solution 1 for ExponomialAssortment.FPTAS.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T08:50:04.469207+00:00
-- url     : https://prove2.me/submissions/016a56c9-817c-41f5-a1ef-4a4c51269a83

import Definitions.Def_ExponomialAssortment_FPTAS_Rounding

open ExponomialAssortment.FPTAS in
theorem solution (n : ℕ) (I : Instance n) (hI : Valid I) (C : ℕ)
    (hC : 1 ≤ C ∧ C ≤ n) (η : ℝ) (hη : 0 < η)
    (S : Finset (Fin n)) (hS : Feasible I C S) (i : Fin n) :
    gapSum I.utility S i - (i.val + 1) * delta n η ≤ gapSum (roundedUtility I η) S i ∧
    gapSum (roundedUtility I η) S i ≤ gapSum I.utility S i + (i.val + 1) * delta n η := by
  have hn : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hC.1.trans hC.2))
  have hd : 0 < delta n η := by unfold delta; positivity
  set d := delta n η with hdd
  have hr : ∀ j, I.utility j - d < roundedUtility I η j ∧ roundedUtility I η j ≤ I.utility j := by
    intro j
    unfold roundedUtility
    rw [← hdd]
    have h1 := Int.floor_le (I.utility j / d)
    have h2 := Int.lt_floor_add_one (I.utility j / d)
    have e : d * (I.utility j / d) = I.utility j := mul_div_cancel₀ _ hd.ne'
    constructor
    · have := mul_lt_mul_of_pos_left h2 hd
      rw [e] at this
      linarith
    · have := mul_le_mul_of_nonneg_left h1 hd.le
      rw [e] at this
      exact this
  have hcard : ((prefixSet S (i.val + 1)).card : ℝ) ≤ i.val + 1 := by
    have : (prefixSet S (i.val + 1)).card ≤ (Finset.range (i.val + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun j : Fin n => j.val)
      · intro j hj
        simp only [prefixSet, Finset.coe_filter, Set.mem_setOf_eq] at hj
        simp only [Finset.coe_range, Set.mem_Iio]
        exact hj.2
      · intro a _ b _ hab
        exact Fin.ext hab
    rw [Finset.card_range] at this
    exact_mod_cast this
  have hsum : ∑ j ∈ prefixSet S (i.val + 1), d = ((prefixSet S (i.val + 1)).card : ℝ) * d := by
    rw [Finset.sum_const, nsmul_eq_mul]
  unfold gapSum
  have hs1 : ∑ j ∈ prefixSet S (i.val + 1), I.utility j -
      ((prefixSet S (i.val + 1)).card : ℝ) * d ≤
      ∑ j ∈ prefixSet S (i.val + 1), roundedUtility I η j := by
    rw [← hsum, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun j _ => by linarith [(hr j).1])
  have hs2 : ∑ j ∈ prefixSet S (i.val + 1), roundedUtility I η j ≤
      ∑ j ∈ prefixSet S (i.val + 1), I.utility j :=
    Finset.sum_le_sum (fun j _ => (hr j).2)
  have hi1 : (1:ℝ) ≤ i.val + 1 := by
    have : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
    linarith
  have hcd := mul_le_mul_of_nonneg_right hcard hd.le
  have hd1 : d ≤ ((i.val : ℝ) + 1) * d := by nlinarith
  constructor
  · linarith [(hr i).2]
  · linarith [(hr i).1]
