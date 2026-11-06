-- Prove2me | solution 1 for ChoicePAC.MidPoint.midpoint_G_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:53:01.681648+00:00
-- url     : https://prove2.me/submissions/34ec6b95-088d-44ae-8f72-76a0b0f3ae9d

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_GF

open ChoicePAC.MidPoint

lemma mp_time_eq (k j : ℕ) (hj : j ≤ (midpointSchedule k).M) :
    (midpointSchedule k).time j = 1 - (1 / 2 : ℝ) ^ j := by
  unfold Schedule.time
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · simp
  · have h1 : j - 1 < (midpointSchedule k).M := by omega
    rw [if_neg (by omega), dif_pos h1]
    show 1 - (1 / 2 : ℝ) ^ ((j - 1) + 1) = _
    rw [Nat.sub_add_cancel hpos]

lemma mp_term (j : ℕ) (u : ℝ) :
    (((1 : ℝ) - (1 / 2 : ℝ) ^ (j + 1)) - (1 - (1 / 2 : ℝ) ^ j)) * u ^ 2 /
      (1 - (1 - (1 / 2 : ℝ) ^ (j + 1))) ^ 2 = 2 ^ (j + 1) * u ^ 2 := by
  have e : (1 / 2 : ℝ) ^ j = 2 * (1 / 2) ^ (j + 1) := by rw [pow_succ]; ring
  have e2 : (2 : ℝ) ^ (j + 1) = 1 / (1 / 2) ^ (j + 1) := by
    rw [one_div_pow, one_div_one_div]
  rw [e, e2]
  generalize hh : (1 / 2 : ℝ) ^ (j + 1) = h
  have h2 : 0 < h := by rw [← hh]; positivity
  rw [show (1 : ℝ) - (1 - h) = h by ring, show (1 - h) - (1 - 2 * h) = h by ring]
  field_simp

lemma geom_sum_Icc (a : ℕ) : ∑ j ∈ Finset.Icc 1 a, (2 : ℝ) ^ j = 2 ^ (a + 1) - 2 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

theorem solution (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht0 : 0 ≤ t)
    (ht : t < (midpointSchedule k).time (midpointSchedule k).M) :
    (midpointSchedule k).G t ≤ 4 * (1 - t) := by
  have hM : (midpointSchedule k).M = Nat.clog 2 k := rfl
  -- M ≥ 1
  have hMpos : 1 ≤ (midpointSchedule k).M := by
    by_contra h
    have h0 : (midpointSchedule k).M = 0 := by omega
    rw [h0] at ht
    simp [Schedule.time] at ht
    linarith
  have htM : t < 1 - (1 / 2 : ℝ) ^ (midpointSchedule k).M := by rwa [mp_time_eq k _ le_rfl] at ht
  have hex : ∃ a : ℕ, t < 1 - (1 / 2 : ℝ) ^ (a + 1) := ⟨(midpointSchedule k).M - 1, by
    rwa [Nat.sub_add_cancel hMpos]⟩
  classical
  set a := Nat.find hex with ha
  have ha_spec : t < 1 - (1 / 2 : ℝ) ^ (a + 1) := Nat.find_spec hex
  have ha_min : ∀ b < a, 1 - (1 / 2 : ℝ) ^ (b + 1) ≤ t := fun b hb =>
    le_of_not_gt (Nat.find_min hex hb)
  have haM : a + 1 ≤ (midpointSchedule k).M := by
    have : a ≤ (midpointSchedule k).M - 1 := Nat.find_min' hex (by rwa [Nat.sub_add_cancel hMpos])
    omega
  have hlow : 1 - (1 / 2 : ℝ) ^ a ≤ t := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h]; simp; exact ht0
    · have := ha_min (a - 1) (by omega)
      rwa [Nat.sub_add_cancel h] at this
  -- idx
  have hidx : (midpointSchedule k).idx t = a + 1 := by
    unfold Schedule.idx
    congr 1
    have hfilt : (Finset.univ.filter (fun l : Fin (midpointSchedule k).M => (midpointSchedule k).t l ≤ t)) =
        Finset.univ.filter (fun l : Fin (midpointSchedule k).M => l.val < a) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      show 1 - (1 / 2 : ℝ) ^ (l.val + 1) ≤ t ↔ _
      constructor
      · intro hl
        by_contra hla
        push Not at hla
        have : (1 / 2 : ℝ) ^ (l.val + 1) ≤ (1 / 2) ^ (a + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        linarith
      · intro hl; exact ha_min _ hl
    rw [hfilt]
    have : (Finset.univ.filter (fun l : Fin (midpointSchedule k).M => l.val < a)) =
        (Finset.range a).attachFin (fun i hi => by simp at hi; omega) := by
      ext l; simp
    rw [this, Finset.card_attachFin, Finset.card_range]
  unfold Schedule.G
  rw [hidx, Nat.add_sub_cancel, mp_time_eq k a (by omega)]
  have hsum : ∑ j ∈ Finset.Icc 1 a, ((midpointSchedule k).time j - (midpointSchedule k).time (j - 1)) * (1 - t) ^ 2 / (1 - (midpointSchedule k).time j) ^ 2
      = ∑ j ∈ Finset.Icc 1 a, (2 : ℝ) ^ j * (1 - t) ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [mp_time_eq k _ (by omega), Nat.add_sub_cancel, mp_time_eq k _ (by omega)]
    exact mp_term j' (1 - t)
  rw [hsum, ← Finset.sum_mul, geom_sum_Icc]
  -- final inequality
  set w : ℝ := (1 / 2) ^ a with hw
  have hwpos : 0 < w := by positivity
  have h2a : (2 : ℝ) ^ (a + 1) = 2 / w := by
    rw [hw, eq_div_iff hwpos.ne', pow_succ, mul_comm _ (2:ℝ), mul_assoc, ← mul_pow]; norm_num
  have hw2 : (1 / 2 : ℝ) ^ (a + 1) = w / 2 := by rw [pow_succ, hw]; ring
  rw [hw2] at ha_spec
  rw [h2a]
  set u := 1 - t with hu
  have hu1 : w / 2 < u := by linarith
  have hu2 : u ≤ w := by linarith
  have key : (t - (1 - w)) + (2 / w - 2) * u ^ 2 ≤ (w - u) + 2 * u ^ 2 / w := by
    have : (2 / w - 2) * u ^ 2 = 2 * u ^ 2 / w - 2 * u ^ 2 := by field_simp
    nlinarith [sq_nonneg u]
  have key2 : (w - u) + 2 * u ^ 2 / w ≤ 4 * u := by
    rw [← sub_nonneg]
    have : 4 * u - ((w - u) + 2 * u ^ 2 / w) = (5 * u * w - w ^ 2 - 2 * u ^ 2) / w := by
      field_simp; ring
    rw [this]
    apply div_nonneg _ hwpos.le
    nlinarith
  linarith
