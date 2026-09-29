-- Prove2me | solution 1 for Freiman.rational_two_cylinder_cover
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:00:06.790351+00:00
-- url     : https://prove2.me/submissions/218b07f1-dd67-4e78-8569-609832701566

import Definitions.Def_Freiman_perronArithmetic
import Definitions.Def_Freiman_rationalCylinderNeighbors
import Theorems.Thm_Freiman_cf_convergence
import Theorems.Thm_Freiman_continuant_denominator_pos
import Mathlib.Tactic.FieldSimp

open Freiman

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace FreimanTwoCylinder

lemma data_append (w : List ℕ+) (a : ℕ+) :
    wordContinuantData (w ++ [a]) =
      ((wordContinuantP w, (a : ℕ) * wordContinuantP w + wordContinuantPrevP w),
       (wordContinuantQ w, (a : ℕ) * wordContinuantQ w + wordContinuantPrevQ w)) := by
  simp [wordContinuantData, List.foldl_append, wordContinuantP,
    wordContinuantQ, wordContinuantPrevP, wordContinuantPrevQ]

lemma data_cons (a : ℕ+) (w : List ℕ+) :
    wordContinuantData (a :: w) =
      ((wordContinuantPrevQ w, wordContinuantQ w),
       ((a : ℕ) * wordContinuantPrevQ w + wordContinuantPrevP w,
        (a : ℕ) * wordContinuantQ w + wordContinuantP w)) := by
  induction w using List.reverseRecOn with
  | nil => simp [wordContinuantData, wordContinuantPrevQ, wordContinuantQ,
      wordContinuantPrevP, wordContinuantP]
  | append_singleton w c ih =>
    rw [show a :: (w ++ [c]) = (a :: w) ++ [c] from rfl, data_append]
    simp only [wordContinuantP, wordContinuantPrevP, wordContinuantQ,
      wordContinuantPrevQ, ih, data_append]
    congr 2
    ring

lemma prevQ_le (w : List ℕ+) : wordContinuantPrevQ w ≤ wordContinuantQ w := by
  induction w using List.reverseRecOn with
  | nil => simp [wordContinuantPrevQ, wordContinuantQ, wordContinuantData]
  | append_singleton w a ih =>
    simp only [wordContinuantPrevQ, wordContinuantQ, data_append]
    change wordContinuantQ w ≤ (a : ℕ) * wordContinuantQ w + wordContinuantPrevQ w
    have ha := a.pos
    nlinarith

lemma right_den_pos (w : List ℕ+) :
    (0 : ℝ) < 2 * (wordContinuantQ w : ℝ) - wordContinuantPrevQ w := by
  have hq : (0 : ℝ) < wordContinuantQ w := by exact_mod_cast continuant_denominator_pos w
  have hp : (wordContinuantPrevQ w : ℝ) ≤ wordContinuantQ w := by exact_mod_cast prevQ_le w
  linarith

lemma left_cons (a : ℕ+) (w : List ℕ+) :
    rationalCylinderNeighborLeft (a :: w) =
      1 / (((a : ℕ) : ℝ) + rationalCylinderNeighborLeft w) := by
  have hd : (wordContinuantQ w : ℝ) + wordContinuantPrevQ w ≠ 0 := by
    have hq : (0 : ℝ) < wordContinuantQ w := by exact_mod_cast continuant_denominator_pos w
    positivity
  simp only [rationalCylinderNeighborLeft, wordContinuantP, wordContinuantQ,
    wordContinuantPrevP, wordContinuantPrevQ, data_cons, Nat.cast_add, Nat.cast_mul]
  change ((wordContinuantQ w : ℝ) + wordContinuantPrevQ w) /
      (((a : ℕ) : ℝ) * wordContinuantQ w + wordContinuantP w +
        (((a : ℕ) : ℝ) * wordContinuantPrevQ w + wordContinuantPrevP w)) =
      1 / (((a : ℕ) : ℝ) + ((wordContinuantP w : ℝ) + wordContinuantPrevP w) /
        ((wordContinuantQ w : ℝ) + wordContinuantPrevQ w))
  rw [add_div_eq_mul_add_div _ _ hd, one_div_div]
  congr 1
  ring

lemma right_cons (a : ℕ+) (w : List ℕ+) :
    rationalCylinderNeighborRight (a :: w) =
      1 / (((a : ℕ) : ℝ) + rationalCylinderNeighborRight w) := by
  have hd := ne_of_gt (right_den_pos w)
  simp only [rationalCylinderNeighborRight, wordContinuantP, wordContinuantQ,
    wordContinuantPrevP, wordContinuantPrevQ, data_cons, Nat.cast_add, Nat.cast_mul]
  change (2 * (wordContinuantQ w : ℝ) - wordContinuantPrevQ w) /
      (2 * (((a : ℕ) : ℝ) * wordContinuantQ w + wordContinuantP w) -
        (((a : ℕ) : ℝ) * wordContinuantPrevQ w + wordContinuantPrevP w)) =
      1 / (((a : ℕ) : ℝ) + (2 * (wordContinuantP w : ℝ) - wordContinuantPrevP w) /
        (2 * (wordContinuantQ w : ℝ) - wordContinuantPrevQ w))
  rw [add_div_eq_mul_add_div _ _ hd, one_div_div]
  congr 1
  ring

lemma digit_ge_one (a : ℕ+) : (1 : ℝ) ≤ (a : ℕ) := by
  exact_mod_cast a.pos

lemma left_singleton (a : ℕ+) : rationalCylinderNeighborLeft [a] =
    1 / (((a : ℕ) : ℝ) + 1) := by
  simp [rationalCylinderNeighborLeft, wordContinuantData, wordContinuantP,
    wordContinuantQ, wordContinuantPrevP, wordContinuantPrevQ]

lemma right_singleton (a : ℕ+) : rationalCylinderNeighborRight [a] =
    1 / (((a : ℕ) : ℝ) - 1 / 2) := by
  rw [right_cons]
  simp [rationalCylinderNeighborRight, wordContinuantData, wordContinuantP,
    wordContinuantQ, wordContinuantPrevP, wordContinuantPrevQ, sub_eq_add_neg]
  norm_num

lemma inv_digit_mem (a : ℕ+) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    1 / (((a : ℕ) : ℝ) + x) ∈ Set.Ioo (0 : ℝ) 1 := by
  have ha := digit_ge_one a
  have hx0 := hx.1
  constructor
  · positivity
  · apply (div_lt_one (by linarith)).2
    linarith [hx.1]

lemma endpoints_mem (w : List ℕ+) (hw : w ≠ [])
    (hlast : 2 ≤ ((w.getLastD 1 : ℕ+) : ℕ)) :
    rationalCylinderNeighborLeft w ∈ Set.Ioo (0 : ℝ) 1 ∧
    rationalCylinderNeighborRight w ∈ Set.Ioo (0 : ℝ) 1 := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons a w ih =>
    by_cases hn : w = []
    · subst w
      have ha : (2 : ℝ) ≤ (a : ℕ) := by
        exact_mod_cast (show 2 ≤ (a : ℕ) by simpa using hlast)
      rw [left_singleton, right_singleton]
      constructor <;> constructor
      · positivity
      · apply (div_lt_one (by linarith)).2
        linarith
      · apply one_div_pos.mpr
        linarith
      · apply (div_lt_one (by linarith)).2
        linarith
    · have ht : 2 ≤ ((w.getLastD 1 : ℕ+) : ℕ) := by
        simpa only [List.getLastD_eq_getLast?, List.getLast?_cons_of_ne_nil hn] using hlast
      have he := ih hn ht
      rw [left_cons, right_cons]
      exact ⟨inv_digit_mem a he.1, inv_digit_mem a he.2⟩

lemma inverse_interval (a d l r : ℝ) (hd : 0 < d)
    (hl : 0 < a + l) (hr : 0 < a + r)
    (hx : 1 / d ∈ Set.Ioo (min (1 / (a + l)) (1 / (a + r)))
      (max (1 / (a + l)) (1 / (a + r)))) :
    d - a ∈ Set.Ioo (min l r) (max l r) := by
  constructor
  · rcases (lt_max_iff).mp hx.2 with h | h
    · have hh := (one_div_lt_one_div hd hl).mp h
      exact lt_of_le_of_lt (min_le_left l r) (by linarith)
    · have hh := (one_div_lt_one_div hd hr).mp h
      exact lt_of_le_of_lt (min_le_right l r) (by linarith)
  · rcases (min_lt_iff).mp hx.1 with h | h
    · have hh := (one_div_lt_one_div hl hd).mp h
      exact lt_of_lt_of_le (by linarith) (le_max_left l r)
    · have hh := (one_div_lt_one_div hr hd).mp h
      exact lt_of_lt_of_le (by linarith) (le_max_right l r)

lemma convergent_succ (b : ℕ → ℕ+) (n : ℕ) :
    cfConvergent b (n + 1) =
      1 / (((b 0 : ℕ) : ℝ) + cfConvergent (fun k => b (k + 1)) n) := by
  simp only [cfConvergent, List.range_succ_eq_map, List.map_cons, List.map_map, finiteCF]
  rfl

lemma cover_singleton (a : ℕ+) (ha : 2 ≤ (a : ℕ)) (b : ℕ → ℕ+)
    (hx : cfValue b ∈ Set.Ioo
      (min (rationalCylinderNeighborLeft [a]) (rationalCylinderNeighborRight [a]))
      (max (rationalCylinderNeighborLeft [a]) (rationalCylinderNeighborRight [a]))) :
    ∃ n : ℕ, cfConvergent b n = finiteCF [a] := by
  let t : ℝ := cfValue (fun k => b (k + 1))
  have ht0 : 0 < t := (cf_convergence (fun k => b (k + 1))).2.2.1
  have ht1 : t < 1 := (cf_convergence (fun k => b (k + 1))).2.2.2.1
  have haR : (2 : ℝ) ≤ (a : ℕ) := by exact_mod_cast ha
  have hbR := digit_ge_one (b 0)
  have hd : 0 < ((b 0 : ℕ) : ℝ) + t := by linarith
  rw [left_singleton, right_singleton, (cf_convergence b).2.2.2.2] at hx
  have hi := inverse_interval ((a : ℕ) : ℝ) (((b 0 : ℕ) : ℝ) + t) 1 (-1 / 2)
    hd (by linarith) (by linarith) (by simpa only [sub_eq_add_neg, neg_div] using hx)
  norm_num at hi
  have hba : (b 0 : ℕ) ≤ (a : ℕ) := by
    by_contra h
    have hN : (a : ℕ) + 1 ≤ (b 0 : ℕ) := by omega
    have hR : ((a : ℕ) : ℝ) + 1 ≤ ((b 0 : ℕ) : ℝ) := by exact_mod_cast hN
    linarith [hi.2]
  have hab : (a : ℕ) ≤ (b 0 : ℕ) + 1 := by
    by_contra h
    have hN : (b 0 : ℕ) + 2 ≤ (a : ℕ) := by omega
    have hR : ((b 0 : ℕ) : ℝ) + 2 ≤ ((a : ℕ) : ℝ) := by exact_mod_cast hN
    linarith [hi.1]
  by_cases heq : b 0 = a
  · refine ⟨1, ?_⟩
    simp [cfConvergent, List.range_succ, finiteCF, heq]
  · have hstep : (b 0 : ℕ) + 1 = (a : ℕ) := by
      have hne : (b 0 : ℕ) ≠ (a : ℕ) := by
        intro h
        exact heq (Subtype.ext h)
      omega
    have hstepR : ((b 0 : ℕ) : ℝ) + 1 = ((a : ℕ) : ℝ) := by exact_mod_cast hstep
    have hhalf : (1 / 2 : ℝ) < t := by linarith [hi.1]
    let s : ℝ := cfValue (fun k => b ((k + 1) + 1))
    have hs0 : 0 < s := (cf_convergence (fun k => b ((k + 1) + 1))).2.2.1
    have ht : t = 1 / (((b 1 : ℕ) : ℝ) + s) := by
      simpa only [t, s, Nat.zero_add] using
        (cf_convergence (fun k => b (k + 1))).2.2.2.2
    have hcR := digit_ge_one (b 1)
    have hden : 0 < ((b 1 : ℕ) : ℝ) + s := by linarith
    rw [ht] at hhalf
    have hlt := (one_div_lt_one_div (by norm_num : (0 : ℝ) < 2) hden).mp hhalf
    have hc : (b 1 : ℕ) < 2 := by
      exact_mod_cast (show ((b 1 : ℕ) : ℝ) < 2 by linarith)
    have hc1 : b 1 = 1 := by
      apply Subtype.ext
      have hp := (b 1).pos
      change (b 1 : ℕ) = 1
      omega
    refine ⟨2, ?_⟩
    simp only [cfConvergent, List.range_succ, List.range_zero,
      List.map_nil, List.map_cons, List.nil_append, List.cons_append,
      finiteCF, hc1, PNat.val_ofNat, Nat.cast_one, add_zero, div_one]
    rw [hstepR]

lemma cover (w : List ℕ+) (hw : w ≠ [])
    (hlast : 2 ≤ ((w.getLastD 1 : ℕ+) : ℕ)) (b : ℕ → ℕ+)
    (hx : cfValue b ∈ Set.Ioo
      (min (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w))
      (max (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w))) :
    ∃ n : ℕ, cfConvergent b n = finiteCF w := by
  induction w generalizing b with
  | nil => exact (hw rfl).elim
  | cons a w ih =>
    by_cases hn : w = []
    · subst w
      exact cover_singleton a (by simpa using hlast) b hx
    · have htlast : 2 ≤ ((w.getLastD 1 : ℕ+) : ℕ) := by
        simpa only [List.getLastD_eq_getLast?, List.getLast?_cons_of_ne_nil hn] using hlast
      have he := endpoints_mem w hn htlast
      let t : ℝ := cfValue (fun k => b (k + 1))
      have ht0 : 0 < t := (cf_convergence (fun k => b (k + 1))).2.2.1
      have ht1 : t < 1 := (cf_convergence (fun k => b (k + 1))).2.2.2.1
      have haR := digit_ge_one a
      have hbR := digit_ge_one (b 0)
      have hd : 0 < ((b 0 : ℕ) : ℝ) + t := by linarith
      rw [left_cons, right_cons, (cf_convergence b).2.2.2.2] at hx
      have hi := inverse_interval ((a : ℕ) : ℝ) (((b 0 : ℕ) : ℝ) + t)
        (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w)
        hd (by linarith [he.1.1]) (by linarith [he.2.1]) hx
      have hlo : 0 < ((b 0 : ℕ) : ℝ) + t - ((a : ℕ) : ℝ) :=
        lt_trans (lt_min he.1.1 he.2.1) hi.1
      have hhi : ((b 0 : ℕ) : ℝ) + t - ((a : ℕ) : ℝ) < 1 :=
        lt_trans hi.2 (max_lt he.1.2 he.2.2)
      have hba : (b 0 : ℕ) ≤ (a : ℕ) := by
        by_contra h
        have hN : (a : ℕ) + 1 ≤ (b 0 : ℕ) := by omega
        have hR : ((a : ℕ) : ℝ) + 1 ≤ ((b 0 : ℕ) : ℝ) := by exact_mod_cast hN
        linarith
      have hab : (a : ℕ) ≤ (b 0 : ℕ) := by
        by_contra h
        have hN : (b 0 : ℕ) + 1 ≤ (a : ℕ) := by omega
        have hR : ((b 0 : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ) := by exact_mod_cast hN
        linarith
      have hfirst : b 0 = a := Subtype.ext (Nat.le_antisymm hba hab)
      have htail : cfValue (fun k => b (k + 1)) ∈ Set.Ioo
          (min (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w))
          (max (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w)) := by
        simpa only [hfirst, add_sub_cancel_left] using hi
      obtain ⟨n, hconv⟩ := ih hn htlast (fun k => b (k + 1)) htail
      refine ⟨n + 1, ?_⟩
      rw [convergent_succ, hfirst, hconv, finiteCF]

end FreimanTwoCylinder

theorem solution (w : List ℕ+) (hw : w ≠ [])
    (hlast : 2 ≤ ((w.getLastD 1 : ℕ+) : ℕ)) (b : ℕ → ℕ+)
    (hx : cfValue b ∈ Set.Ioo
      (min (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w))
      (max (rationalCylinderNeighborLeft w) (rationalCylinderNeighborRight w))) :
    ∃ n : ℕ, cfConvergent b n = finiteCF w :=
  FreimanTwoCylinder.cover w hw hlast b hx
