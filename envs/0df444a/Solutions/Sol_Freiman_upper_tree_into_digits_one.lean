-- Prove2me | solution 1 for Freiman.upper_tree_into_digits_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T21:19:56.473311+00:00
-- url     : https://prove2.me/submissions/8741674f-ba50-4e3c-8847-67c5cfe51352

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_cf_convergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_Freiman_cfValue_prefix
import Definitions.Def_Freiman_gapModel
import Theorems.Thm_Freiman_bounded_words_subsequence
import Theorems.Thm_Freiman_cfValue_cylinder_bound
import Theorems.Thm_Freiman_cylinder_bound_tendsto
import Mathlib.Topology.Sequences
import Theorems.Thm_Freiman_prefixEval_cylinder_bound
import Theorems.Thm_Freiman_upper_mesh_from_prefix_bounds
import Theorems.Thm_Freiman_upper_tree_word_growth

set_option autoImplicit false
set_option maxHeartbeats 800000
open Freiman

namespace UpperTreeIntoDigitsOneOrder

set_option autoImplicit false
set_option maxHeartbeats 800000
open Freiman

namespace FreimanGapOrderProof

lemma first_lt (b c : ℕ → ℕ+) (hd : c 0 < b 0) : cfValue b < cfValue c := by
  have hb := cf_convergence (fun k => b (k + 1))
  have hc := cf_convergence (fun k => c (k + 1))
  have hdb : (0 : ℝ) < (b 0 : ℕ) := by exact_mod_cast (b 0).pos
  have hdc : (0 : ℝ) < (c 0 : ℕ) := by exact_mod_cast (c 0).pos
  have hn : (c 0 : ℕ) + 1 ≤ (b 0 : ℕ) := hd
  have hnR : ((c 0 : ℕ) : ℝ) + 1 ≤ ((b 0 : ℕ) : ℝ) := by exact_mod_cast hn
  rw [(cf_convergence b).2.2.2.2, (cf_convergence c).2.2.2.2]
  apply (div_lt_div_iff₀ (by linarith [hb.2.2.1]) (by linarith [hc.2.2.1])).2
  linarith [hb.2.2.1, hc.2.2.2.1]

lemma tail_reverse (b c : ℕ → ℕ+) (hd : b 0 = c 0) :
    cfValue b < cfValue c ↔
      cfValue (fun k => c (k + 1)) < cfValue (fun k => b (k + 1)) := by
  have hb := cf_convergence (fun k => b (k + 1))
  have hc := cf_convergence (fun k => c (k + 1))
  have hdc : (0 : ℝ) < (c 0 : ℕ) := by exact_mod_cast (c 0).pos
  rw [(cf_convergence b).2.2.2.2, (cf_convergence c).2.2.2.2, hd]
  rw [div_lt_div_iff₀ (by linarith [hb.2.2.1]) (by linarith [hc.2.2.1])]
  simp only [one_mul, add_lt_add_iff_left]

end FreimanGapOrderProof

open FreimanGapOrderProof in
theorem gap_first_difference (b c : ℕ → ℕ+) (n : ℕ) (hprefix : gapSameBefore b c n)
    (hd : b n ≠ c n) :
    (cfValue b < cfValue c ↔ if Even n then c n < b n else b n < c n) := by
  induction n generalizing b c with
  | zero =>
    rw [if_pos (show Even (0 : ℕ) from ⟨0, by omega⟩)]
    constructor
    · intro hv
      rcases lt_or_gt_of_ne hd with hlt | hgt
      · exact False.elim ((first_lt c b hlt).not_gt hv)
      · exact hgt
    · exact first_lt b c
  | succ n ih =>
    have hzero : b 0 = c 0 := hprefix 0 (by omega)
    have hp : gapSameBefore (fun k => c (k + 1)) (fun k => b (k + 1)) n := by
      intro k hk
      exact (hprefix (k + 1) (by omega)).symm
    have hd' : c (n + 1) ≠ b (n + 1) := Ne.symm hd
    rw [tail_reverse b c hzero, ih _ _ hp hd']
    by_cases he : Even n <;> simp [Nat.even_add_one, he]

set_option autoImplicit false
open Freiman

theorem gap_comparison
    (horder : ∀ (b c : ℕ → ℕ+) (n : ℕ), gapSameBefore b c n → b n ≠ c n →
      (cfValue b < cfValue c ↔ if Even n then c n < b n else b n < c n))
    (b c : ℕ → ℕ+) :
    ((∀ n, gapSameBefore b c n → gapUpperDigit b c n) → cfValue b ≤ cfValue c) ∧
    ((∀ n, gapSameBefore b c n → gapLowerDigit b c n) → cfValue c ≤ cfValue b) := by
  classical
  have main (u v : ℕ → ℕ+)
      (h : ∀ n, gapSameBefore u v n → gapUpperDigit u v n) : cfValue u ≤ cfValue v := by
    by_cases heq : u = v
    · simp [heq]
    have hex : ∃ n : ℕ, u n ≠ v n := by
      by_contra hx
      apply heq
      funext n
      by_contra hn
      exact hx ⟨n, hn⟩
    let n := Nat.find hex
    have hd : u n ≠ v n := Nat.find_spec hex
    have hp : gapSameBefore u v n := by
      intro k hk
      by_contra hneq
      exact (Nat.not_le_of_gt hk) (Nat.find_min' hex hneq)
    apply ((horder u v n hp hd).2 ?_).le
    have hh := h n hp
    by_cases he : Even n
    · simp only [gapUpperDigit, he, if_true] at hh ⊢
      exact lt_of_le_of_ne hh (Ne.symm hd)
    · simp only [gapUpperDigit, he, if_false] at hh ⊢
      exact lt_of_le_of_ne hh hd
  refine ⟨main b c, ?_⟩
  intro h
  apply main c b
  intro n hp
  have hp' : gapSameBefore b c n := fun k hk => (hp k hk).symm
  simpa [gapUpperDigit, gapLowerDigit] using h n hp'
end UpperTreeIntoDigitsOneOrder

namespace UpperTreeIntoDigitsOneKABounds

def period (n : ℕ) : ℕ+ := if Even n then 1 else 3

lemma period_value : cfValue period = upperTheta1 := by
  have hprefix : (List.range 2).map period = [1, 3] := by
    norm_num [List.range_succ, period, Nat.even_iff]
  have htail : (fun n => period (2 + n)) = period := by
    funext n
    simp [period, Nat.even_add]
  have hf := cfValue_prefix period 2
  rw [hprefix, htail] at hf
  norm_num [prefixEval] at hf
  have hp := (cf_convergence period).2.2.1
  have hd : (3 : ℝ) + cfValue period ≠ 0 := by linarith
  have hd' : (4 : ℝ) + cfValue period ≠ 0 := by linarith
  field_simp at hf
  have hpoly : cfValue period ^ 2 + 3 * cfValue period - 3 = 0 := by nlinarith [hf]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)
  have hs0 := Real.sqrt_nonneg (21 : ℝ)
  have he : (2 * cfValue period + 3) ^ 2 = (Real.sqrt 21) ^ 2 := by nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · dsimp [upperTheta1]
    linarith
  · exfalso
    linarith

lemma upper_bound (b : ℕ → ℕ+) (hb : upperAdmissible b) :
    cfValue b ≤ upperTheta1 := by
  rw [← period_value]
  apply (UpperTreeIntoDigitsOneOrder.gap_comparison UpperTreeIntoDigitsOneOrder.gap_first_difference b period).1
  intro n hp
  by_cases he : Even n
  · simpa [gapUpperDigit, period, he] using
      (show (1 : ℕ+) ≤ b n from (b n).pos)
  · have hn : (b n : ℕ) ≤ 3 := by
      cases n with
      | zero => exact False.elim (he ⟨0, rfl⟩)
      | succ k =>
        have hk : Even k := by simpa [Nat.even_add_one] using he
        have hprev := hp k (by omega)
        have hbprev : (b k : ℕ) ≤ 2 := by simp [hprev, period, hk]
        exact hb.2 k hbprev
    have hn' : b n ≤ (3 : ℕ+) := hn
    simpa [gapUpperDigit, period, he] using hn'

end UpperTreeIntoDigitsOneKABounds

open UpperTreeIntoDigitsOneKABounds in
private theorem ka_bound (x : ℝ) (hx : x ∈ upperKA) :
    x ∈ Set.Icc upperTheta8 upperTheta1 := by
  obtain ⟨b, hb, rfl⟩ := hx
  refine ⟨?_, upper_bound b hb⟩
  have htail : upperAdmissible (fun n => b (n + 1)) := by
    exact ⟨fun n => hb.1 (n + 1), fun n hn => hb.2 (n + 1) hn⟩
  have hu := upper_bound (fun n => b (n + 1)) htail
  have hp := (cf_convergence (fun n => b (n + 1))).2.2.1
  have hd0 : (0 : ℝ) < (b 0 : ℕ) := by exact_mod_cast (b 0).pos
  have hd4 : ((b 0 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hb.1 0
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)
  have hs0 := Real.sqrt_nonneg (21 : ℝ)
  have hden : 0 < 4 + upperTheta1 := by dsimp [upperTheta1]; linarith
  have he : 1 / (4 + upperTheta1) = upperTheta8 := by
    apply (div_eq_iff (ne_of_gt hden)).2
    dsimp [upperTheta1, upperTheta8]
    nlinarith
  rw [← he, (cf_convergence b).2.2.2.2]
  apply (div_le_div_iff₀ hden (by linarith)).2
  nlinarith

set_option maxHeartbeats 1000000
open Freiman

namespace UpperTreeIntoDigitsOne

lemma prefix_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

def tail (b : ℕ → ℕ+) (n : ℕ) : ℕ+ := b (n + 1)

def allowed (k : Fin 5) (b : ℕ → ℕ+) : Prop :=
  upperAdmissible b ∧
    match k.val with
    | 0 => True
    | 1 => 2 ≤ (b 0 : ℕ)
    | 2 => 3 ≤ (b 0 : ℕ)
    | 3 => (b 0 : ℕ) ≤ 3
    | _ => 2 ≤ (b 0 : ℕ) ∧ (b 0 : ℕ) ≤ 3

def sem (s : upperState) (x : ℝ) : Prop :=
  ∃ b, allowed s.row b ∧ x = prefixEval s.word (cfValue b)

lemma tail_admissible (b : ℕ → ℕ+) (hb : upperAdmissible b) :
    upperAdmissible (tail b) :=
  ⟨fun n => hb.1 (n + 1), fun n hn => hb.2 (n + 1) hn⟩

lemma prefix_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    dsimp [prefixEval]
    apply div_nonneg (by norm_num)
    have ha : (0 : ℝ) ≤ (a : ℕ) := by positivity
    linarith

lemma prefix_between (w : List ℕ+) (l x r : ℝ) (hl : 0 ≤ l)
    (hlx : l ≤ x) (hxr : x ≤ r) :
    min (prefixEval w l) (prefixEval w r) ≤ prefixEval w x ∧
    prefixEval w x ≤ max (prefixEval w l) (prefixEval w r) := by
  induction w with
  | nil => simpa [prefixEval, min_eq_left (hlx.trans hxr), max_eq_right (hlx.trans hxr)] using And.intro hlx hxr
  | cons a w ih =>
    have ha : (0 : ℝ) < (a : ℕ) := by exact_mod_cast a.pos
    have hL : 0 < (a : ℕ) + prefixEval w l := by linarith [prefix_nonneg w l hl]
    have hX : 0 < (a : ℕ) + prefixEval w x := by linarith [prefix_nonneg w x (hl.trans hlx)]
    have hR : 0 < (a : ℕ) + prefixEval w r := by linarith [prefix_nonneg w r (hl.trans (hlx.trans hxr))]
    rcases le_total (prefixEval w l) (prefixEval w r) with h | h
    · rw [min_eq_left h, max_eq_right h] at ih
      have hlow := one_div_le_one_div_of_le hX (add_le_add_right ih.2 ((a : ℕ) : ℝ))
      have hupp := one_div_le_one_div_of_le hL (add_le_add_right ih.1 ((a : ℕ) : ℝ))
      dsimp only [prefixEval]
      rw [min_eq_right (hlow.trans hupp), max_eq_left (hlow.trans hupp)]
      exact ⟨hlow, hupp⟩
    · rw [min_eq_right h, max_eq_left h] at ih
      have hlow := one_div_le_one_div_of_le hX (add_le_add_right ih.2 ((a : ℕ) : ℝ))
      have hupp := one_div_le_one_div_of_le hR (add_le_add_right ih.1 ((a : ℕ) : ℝ))
      dsimp only [prefixEval]
      rw [min_eq_left (hlow.trans hupp), max_eq_right (hlow.trans hupp)]
      exact ⟨hlow, hupp⟩

lemma constants :
    0 < upperTheta8 ∧ 0 < upperTheta6 ∧
    1 / (3 + upperTheta1) = upperTheta6 ∧
    1 / (3 + upperTheta8) = upperTheta5 ∧
    1 / (2 + upperTheta6) = upperTheta3 ∧
    upperTheta5 ≤ upperTheta3 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hs0 := Real.sqrt_nonneg (21 : ℝ)
  have h4 : (4 : ℝ) < Real.sqrt 21 := by nlinarith
  have h5 : Real.sqrt 21 < (5 : ℝ) := by nlinarith
  have hd1 : 3 + upperTheta1 ≠ 0 := by dsimp [upperTheta1]; linarith
  have hd2 : 3 + upperTheta8 ≠ 0 := by dsimp [upperTheta8]; linarith
  have hd3 : 2 + upperTheta6 ≠ 0 := by dsimp [upperTheta6]; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [upperTheta8]; linarith
  · dsimp [upperTheta6]; linarith
  · apply (div_eq_iff hd1).2
    dsimp [upperTheta1, upperTheta6]; nlinarith
  · apply (div_eq_iff hd2).2
    dsimp [upperTheta8, upperTheta5]; nlinarith
  · apply (div_eq_iff hd3).2
    dsimp [upperTheta6, upperTheta3]; nlinarith
  · dsimp [upperTheta5, upperTheta3]; linarith

lemma row_bounds
    (hKA : ∀ x ∈ upperKA, x ∈ Set.Icc upperTheta8 upperTheta1)
    (k : Fin 5) (b : ℕ → ℕ+) (hb : allowed k b) :
    cfValue b ∈ upperIntervalSet (upperRows k).parent := by
  have hall := hKA (cfValue b) ⟨b, hb.1, rfl⟩
  have ht := hKA (cfValue (tail b)) ⟨tail b, tail_admissible b hb.1, rfl⟩
  have htp := (cf_convergence (tail b)).2.2.1
  have hbp : (0 : ℝ) < (b 0 : ℕ) := by exact_mod_cast (b 0).pos
  have he : cfValue b = 1 / ((b 0 : ℕ) + cfValue (tail b)) :=
    (cf_convergence b).2.2.2.2
  have lowerB : ∀ c : ℕ → ℕ+, upperAdmissible c → (c 0 : ℕ) ≤ 3 →
      upperTheta6 ≤ cfValue c := by
    intro c hc hc3
    have hc' : ((c 0 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hc3
    have hct := hKA (cfValue (tail c)) ⟨tail c, tail_admissible c hc, rfl⟩
    have hcp := (cf_convergence (tail c)).2.2.1
    have hcd : (0 : ℝ) < (c 0 : ℕ) := by exact_mod_cast (c 0).pos
    rw [← constants.2.2.1, (cf_convergence c).2.2.2.2]
    exact one_div_le_one_div_of_le
      (by change 0 < (c 0 : ℕ) + cfValue (tail c); linarith)
      (by change (c 0 : ℕ) + cfValue (tail c) ≤ 3 + upperTheta1; linarith [hct.2])
  have upper3 (h : 3 ≤ (b 0 : ℕ)) : cfValue b ≤ upperTheta5 := by
    have h' : (3 : ℝ) ≤ (b 0 : ℕ) := by exact_mod_cast h
    rw [he, ← constants.2.2.2.1]
    exact one_div_le_one_div_of_le (by linarith [constants.1]) (by linarith [ht.1])
  have upper2 (h : 2 ≤ (b 0 : ℕ)) : cfValue b ≤ upperTheta3 := by
    by_cases h2 : (b 0 : ℕ) = 2
    · have hnext := hb.1.2 0 (by omega)
      have htlo := lowerB (tail b) (tail_admissible b hb.1) (by simpa [tail] using hnext)
      rw [he, h2, ← constants.2.2.2.2.1]
      norm_num only [Nat.cast_ofNat]
      exact one_div_le_one_div_of_le (by linarith [constants.2.1]) (by linarith)
    · exact (upper3 (by omega)).trans constants.2.2.2.2.2
  fin_cases k
  · exact hall
  · exact ⟨hall.1, upper2 hb.2⟩
  · exact ⟨hall.1, upper3 hb.2⟩
  · exact ⟨lowerB b hb.1 hb.2, hall.2⟩
  · exact ⟨lowerB b hb.1 hb.2.2, upper2 hb.2.1⟩

lemma row_left_nonneg (k : Fin 5) : 0 ≤ (upperRows k).parent.left := by
  fin_cases k
  · exact constants.1.le
  · exact constants.1.le
  · exact constants.1.le
  · exact constants.2.1.le
  · exact constants.2.1.le

lemma sem_mem
    (hKA : ∀ x ∈ upperKA, x ∈ Set.Icc upperTheta8 upperTheta1)
    (s : upperState) (x : ℝ) (hx : sem s x) :
    x ∈ upperIntervalSet (upperImage s.word (upperRows s.row).parent) := by
  obtain ⟨b, hb, rfl⟩ := hx
  have h := row_bounds hKA s.row b hb
  exact prefix_between s.word _ _ _ (row_left_nonneg s.row) h.1 h.2


def next (s : upperState) (b : Bool) : upperState :=
  match s.row.val, b with
  | 0, false => ⟨s.word, 1⟩
  | 0, true => ⟨s.word ++ [1], 3⟩
  | 1, false => ⟨s.word, 2⟩
  | 1, true => ⟨s.word ++ [2], 3⟩
  | 2, false => ⟨s.word ++ [4], 0⟩
  | 2, true => ⟨s.word ++ [3], 0⟩
  | 3, false => ⟨s.word, 4⟩
  | 3, true => ⟨s.word ++ [1], 3⟩
  | _, false => ⟨s.word ++ [3], 0⟩
  | _, true => ⟨s.word ++ [2], 3⟩

lemma next_physical (s : upperState) (b : Bool) :
    upperNextState s (if s.word.length % 2 = 0 then b else !b) = next s b := by
  obtain ⟨p, k⟩ := s
  fin_cases k <;> cases b <;> by_cases h : p.length % 2 = 0 <;>
    simp [upperNextState, next, h]

lemma consume (p : List ℕ+) (b : ℕ → ℕ+) (d : ℕ+) (h : b 0 = d) :
    prefixEval p (cfValue b) = prefixEval (p ++ [d]) (cfValue (tail b)) := by
  rw [prefix_append, (cf_convergence b).2.2.2.2, h]
  rfl

lemma step_exists (s : upperState) (x : ℝ) (hx : sem s x) :
    ∃ a : Bool, sem (upperNextState s a) x := by
  obtain ⟨p, k⟩ := s
  obtain ⟨b, hb, rfl⟩ := hx
  have hp := (b 0).pos
  have h4 := hb.1.1 0
  have ht := tail_admissible b hb.1
  suffices h : ∃ a : Bool, sem (next ⟨p, k⟩ a) (prefixEval p (cfValue b)) by
    obtain ⟨a, ha⟩ := h
    exact ⟨if p.length % 2 = 0 then a else !a, by rw [next_physical]; exact ha⟩
  fin_cases k
  · by_cases hd : (b 0 : ℕ) = 1
    · refine ⟨true, tail b, ⟨ht, ?_⟩, consume p b 1 ?_⟩
      · exact hb.1.2 0 (by omega)
      · apply Subtype.ext; exact hd
    · exact ⟨false, b, ⟨hb.1, by change 2 ≤ (b 0 : ℕ); omega⟩, rfl⟩
  · by_cases hd : (b 0 : ℕ) = 2
    · refine ⟨true, tail b, ⟨ht, ?_⟩, consume p b 2 ?_⟩
      · exact hb.1.2 0 (by omega)
      · apply Subtype.ext; exact hd
    · refine ⟨false, b, ⟨hb.1, ?_⟩, rfl⟩
      have hh : 2 ≤ (b 0 : ℕ) := hb.2
      change 3 ≤ (b 0 : ℕ)
      omega
  · by_cases hd : (b 0 : ℕ) = 3
    · refine ⟨true, tail b, ⟨ht, trivial⟩, consume p b 3 ?_⟩
      apply Subtype.ext; exact hd
    · refine ⟨false, tail b, ⟨ht, trivial⟩, consume p b 4 ?_⟩
      have hh : 3 ≤ (b 0 : ℕ) := hb.2
      apply Subtype.ext; change (b 0 : ℕ) = 4; omega
  · by_cases hd : (b 0 : ℕ) = 1
    · refine ⟨true, tail b, ⟨ht, ?_⟩, consume p b 1 ?_⟩
      · exact hb.1.2 0 (by omega)
      · apply Subtype.ext; exact hd
    · exact ⟨false, b, ⟨hb.1, ⟨by omega, hb.2⟩⟩, rfl⟩
  · by_cases hd : (b 0 : ℕ) = 2
    · refine ⟨true, tail b, ⟨ht, ?_⟩, consume p b 2 ?_⟩
      · exact hb.1.2 0 (by omega)
      · apply Subtype.ext; exact hd
    · refine ⟨false, tail b, ⟨ht, trivial⟩, consume p b 3 ?_⟩
      have hh : 2 ≤ (b 0 : ℕ) ∧ (b 0 : ℕ) ≤ 3 := hb.2
      apply Subtype.ext; change (b 0 : ℕ) = 3; omega

lemma sem_levels (s : upperState) (x : ℝ) (hx : sem s x) :
    ∀ n : ℕ, ∃ w : List Bool, w.length = n ∧ sem (upperStateAt s w) x := by
  intro n
  induction n with
  | zero => exact ⟨[], rfl, hx⟩
  | succ n ih =>
    obtain ⟨w, hw, hxw⟩ := ih
    obtain ⟨a, ha⟩ := step_exists (upperStateAt s w) x hxw
    refine ⟨w ++ [a], by simp [hw], ?_⟩
    simpa [upperStateAt, List.foldl_append] using ha

lemma sem_tree
    (hKA : ∀ x ∈ upperKA, x ∈ Set.Icc upperTheta8 upperTheta1)
    (p : List ℕ+) (k : Fin 5) (x : ℝ) (hx : sem ⟨p, k⟩ x) :
    x ∈ upperTreeSet (upperTree p k) := by
  intro n
  obtain ⟨w, hw, hsem⟩ := sem_levels ⟨p, k⟩ x hx n
  exact ⟨w, hw, sem_mem hKA _ x hsem⟩


lemma tree_approx
    (hKA : ∀ x ∈ upperKA, x ∈ Set.Icc upperTheta8 upperTheta1)
    (hback : ∀ s w x, sem (upperStateAt s w) x → sem s x)
    (hne : ∀ s, ∃ x, sem s x)
    (p : List ℕ+) (k : Fin 5) (hm : upperMesh (upperTree p k))
    (x : ℝ) (hx : x ∈ upperTreeSet (upperTree p k)) :
    ∀ ε : ℝ, 0 < ε → ∃ y, sem ⟨p, k⟩ y ∧ dist x y < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hm (ε / 2) (by linarith)
  obtain ⟨w, hw, hxw⟩ := hx N
  obtain ⟨y, hy⟩ := hne (upperStateAt ⟨p, k⟩ w)
  refine ⟨y, hback ⟨p, k⟩ w y hy, ?_⟩
  have hyw := sem_mem hKA (upperStateAt ⟨p, k⟩ w) y hy
  change y ∈ upperIntervalSet (upperTree p k w) at hyw
  have hd : dist x y ≤ upperLength (upperTree p k w) := by
    rw [Real.dist_eq]
    apply abs_sub_le_iff.mpr
    dsimp only [upperIntervalSet, Set.mem_Icc] at hxw hyw
    dsimp only [upperLength]
    constructor <;> linarith [hxw.1, hxw.2, hyw.1, hyw.2]
  exact hd.trans_lt ((hN w (by omega)).trans_lt (by linarith))

end UpperTreeIntoDigitsOne

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Freiman

namespace UpperTreeIntoDigitsOne

def prepend (d : ℕ+) (b : ℕ → ℕ+) : ℕ → ℕ+
  | 0 => d
  | n + 1 => b n

lemma prepend_admissible (d : ℕ+) (b : ℕ → ℕ+)
    (hb : upperAdmissible b) (hd : (d : ℕ) ≤ 4)
    (hnext : (d : ℕ) ≤ 2 → (b 0 : ℕ) ≤ 3) :
    upperAdmissible (prepend d b) := by
  constructor
  · intro n
    cases n with
    | zero => exact hd
    | succ n => exact hb.1 n
  · intro n hn
    cases n with
    | zero => exact hnext hn
    | succ n => exact hb.2 n hn

lemma prepend_value (p : List ℕ+) (d : ℕ+) (b : ℕ → ℕ+) :
    prefixEval (p ++ [d]) (cfValue b) = prefixEval p (cfValue (prepend d b)) := by
  symm
  have ht : tail (prepend d b) = b := by funext n; rfl
  simpa only [ht] using consume p (prepend d b) d rfl

lemma sem_prepend (p : List ℕ+) (k l : Fin 5) (d : ℕ+) (x : ℝ)
    (h : sem ⟨p ++ [d], l⟩ x)
    (ha : ∀ b, allowed l b → allowed k (prepend d b)) :
    sem ⟨p, k⟩ x := by
  obtain ⟨b, hb, hx⟩ := h
  exact ⟨prepend d b, ha b hb, hx.trans (prepend_value p d b)⟩

lemma next_backward (s : upperState) (x : ℝ) (a : Bool)
    (hx : sem (next s a) x) : sem s x := by
  obtain ⟨p, k⟩ := s
  fin_cases k <;> cases a
  · obtain ⟨b, hb, hx⟩ := hx
    exact ⟨b, ⟨hb.1, trivial⟩, hx⟩
  · apply sem_prepend p 0 3 1 x hx
    intro b hb
    exact ⟨prepend_admissible 1 b hb.1 (by norm_num) (fun _ => hb.2), trivial⟩
  · obtain ⟨b, hb, hx⟩ := hx
    refine ⟨b, ⟨hb.1, ?_⟩, hx⟩
    have h : 3 ≤ (b 0 : ℕ) := hb.2
    change 2 ≤ (b 0 : ℕ)
    omega
  · apply sem_prepend p 1 3 2 x hx
    intro b hb
    exact ⟨prepend_admissible 2 b hb.1 (by norm_num) (fun _ => hb.2), by norm_num [prepend]⟩
  · apply sem_prepend p 2 0 4 x hx
    intro b hb
    exact ⟨prepend_admissible 4 b hb.1 (by norm_num) (by norm_num), by norm_num [prepend]⟩
  · apply sem_prepend p 2 0 3 x hx
    intro b hb
    exact ⟨prepend_admissible 3 b hb.1 (by norm_num) (by norm_num), by norm_num [prepend]⟩
  · obtain ⟨b, hb, hx⟩ := hx
    exact ⟨b, ⟨hb.1, hb.2.2⟩, hx⟩
  · apply sem_prepend p 3 3 1 x hx
    intro b hb
    exact ⟨prepend_admissible 1 b hb.1 (by norm_num) (fun _ => hb.2), by norm_num [prepend]⟩
  · apply sem_prepend p 4 0 3 x hx
    intro b hb
    exact ⟨prepend_admissible 3 b hb.1 (by norm_num) (by norm_num), by norm_num [prepend]⟩
  · apply sem_prepend p 4 3 2 x hx
    intro b hb
    exact ⟨prepend_admissible 2 b hb.1 (by norm_num) (fun _ => hb.2), by norm_num [prepend]⟩

lemma step_backward (s : upperState) (x : ℝ) (a : Bool)
    (hx : sem (upperNextState s a) x) : sem s x := by
  by_cases hp : s.word.length % 2 = 0
  · have he := next_physical s a
    rw [if_pos hp] at he
    rw [he] at hx
    exact next_backward s x a hx
  · have he := next_physical s (!a)
    rw [if_neg hp, Bool.not_not] at he
    rw [he] at hx
    exact next_backward s x (!a) hx

lemma sem_nonempty (s : upperState) : ∃ x, sem s x := by
  let b : ℕ → ℕ+ := fun _ => 3
  have hb : upperAdmissible b := by
    constructor
    · intro n; norm_num [b]
    · intro n hn; norm_num [b]
  refine ⟨prefixEval s.word (cfValue b), b, ⟨hb, ?_⟩, rfl⟩
  have hrow := s.row.isLt
  rcases s with ⟨p, k⟩
  fin_cases k <;> norm_num [b]

lemma path_backward (s : upperState) (w : List Bool) (x : ℝ)
    (hx : sem (upperStateAt s w) x) : sem s x := by
  induction w generalizing s with
  | nil => exact hx
  | cons a w ih =>
    apply step_backward s x a
    apply ih
    exact hx

end UpperTreeIntoDigitsOne

set_option autoImplicit false
set_option maxHeartbeats 800000

open Freiman Filter Topology

private theorem upper_digits_tendsto (A : ℕ → ℕ → ℕ+) (b : ℕ → ℕ+)
    (h : ∀ k, ∀ᶠ n in atTop, A n k = b k) :
    Tendsto (fun n => cfValue (A n)) atTop (nhds (cfValue b)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m, hm⟩ := ((tendsto_order.mp cylinder_bound_tendsto).2 ε hε).exists
  have hh : ∀ᶠ n in atTop, ∀ k ∈ Finset.range m, A n k = b k :=
    (Filter.eventually_all_finset _).mpr (fun k _ => h k)
  filter_upwards [hh] with n hn
  rw [Real.dist_eq]
  exact (cfValue_cylinder_bound (A n) b m (fun k hk => hn k (Finset.mem_range.mpr hk))).trans_lt
    ((div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (sq_nonneg _)).trans_lt hm)

private theorem upper_admissible_compact (N : ℕ) :
    IsCompact {x : ℝ | ∃ b : ℕ → ℕ+, upperAdmissible b ∧ (b 0 : ℕ) ≤ N ∧ x = cfValue b} := by
  apply IsSeqCompact.isCompact
  intro x hx
  choose A hA hN hvalue using hx
  obtain ⟨v, hv, c, hc, hcv⟩ := bounded_words_subsequence
    (fun n i => A n i.toNat) 4 (fun i => Eventually.of_forall (fun n => (hA n).1 _))
  let b : ℕ → ℕ+ := fun k => c k
  have hb : ∀ k, (b k : ℕ) ≤ 4 := fun k => hc k
  have hstab : ∀ k, ∀ᶠ n in atTop, A (v n) k = b k := by
    intro k
    simpa only [b, Int.toNat_natCast] using hcv (k : ℤ)
  have had : upperAdmissible b := by
    refine ⟨hb, ?_⟩
    intro k hk
    obtain ⟨n, hn, hn'⟩ := ((hstab k).and (hstab (k + 1))).exists
    rw [← hn']
    exact (hA (v n)).2 k (by rwa [hn])
  have hbN : (b 0 : ℕ) ≤ N := by
    obtain ⟨n, hn⟩ := (hstab 0).exists
    rw [← hn]
    exact hN (v n)
  refine ⟨cfValue b, ⟨b, had, hbN, rfl⟩, v, hv, ?_⟩
  have heq : (x ∘ v) = (fun n => cfValue (A (v n))) := by
    funext n
    exact hvalue (v n)
  rw [heq]
  exact upper_digits_tendsto (fun n => A (v n)) b hstab

private theorem upperKA_isCompact : IsCompact upperKA := by
  have heq : upperKA = {x : ℝ | ∃ b : ℕ → ℕ+, upperAdmissible b ∧
      (b 0 : ℕ) ≤ 4 ∧ x = cfValue b} := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, hb.1 0, rfl⟩
    · rintro ⟨b, hb, _, rfl⟩
      exact ⟨b, hb, rfl⟩
  rw [heq]
  exact upper_admissible_compact 4

private theorem upperKB_isCompact : IsCompact upperKB := by
  exact upper_admissible_compact 3

private theorem upperKOne_isCompact : IsCompact upperKOne := by
  apply upperKB_isCompact.image_of_continuousOn
  intro x hx
  have hpos : 0 < x := by
    obtain ⟨b, _, _, rfl⟩ := hx
    exact (cf_convergence b).2.2.1
  exact continuousWithinAt_const.div
    (continuousWithinAt_const.add continuousWithinAt_id) (by linarith)

open Freiman

private theorem row_endpoints (k : Fin 5) :
    (upperRows k).parent.left ∈ Set.Icc (0 : ℝ) 1 ∧
    (upperRows k).parent.right ∈ Set.Icc (0 : ℝ) 1 := by
  have hs0 := Real.sqrt_nonneg (21 : ℝ)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hlo : (4 : ℝ) < Real.sqrt 21 := by nlinarith
  have hhi : Real.sqrt 21 < (5 : ℝ) := by nlinarith
  have h1 : upperTheta1 ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [upperTheta1]; constructor <;> nlinarith
  have h3 : upperTheta3 ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [upperTheta3]; constructor <;> nlinarith
  have h5 : upperTheta5 ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [upperTheta5]; constructor <;> nlinarith
  have h6 : upperTheta6 ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [upperTheta6]; constructor <;> nlinarith
  have h8 : upperTheta8 ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [upperTheta8]; constructor <;> nlinarith
  fin_cases k
  · exact ⟨h8, h1⟩
  · exact ⟨h8, h3⟩
  · exact ⟨h8, h5⟩
  · exact ⟨h6, h1⟩
  · exact ⟨h6, h3⟩

private theorem node_width (p : List ℕ+) (k : Fin 5) (w : List Bool) :
    upperLength (upperTree p k w) ≤
    1 / (((Nat.fib ((upperStateAt ⟨p, k⟩ w).word.length + 1) : ℕ) : ℝ) ^ 2) := by
  let s := upperStateAt ⟨p, k⟩ w
  have h := prefixEval_cylinder_bound s.word (upperRows s.row).parent.left
    (upperRows s.row).parent.right (row_endpoints s.row).1 (row_endpoints s.row).2
  change max (prefixEval s.word (upperRows s.row).parent.left)
      (prefixEval s.word (upperRows s.row).parent.right) -
    min (prefixEval s.word (upperRows s.row).parent.left)
      (prefixEval s.word (upperRows s.row).parent.right) ≤ _
  rw [max_sub_min_eq_abs, abs_sub_comm]
  exact h

private theorem node_mesh (p : List ℕ+) (k : Fin 5) : upperMesh (upperTree p k) := by
  exact upper_mesh_from_prefix_bounds (upperTree p k)
    (fun w => (upperStateAt ⟨p, k⟩ w).word.length)
    (upper_tree_word_growth p k) (node_width p k)


theorem solution : upperTreeSet (upperTree [1] 3) ⊆ upperKOne := by
  intro x hx
  apply (Metric.mem_of_closed' upperKOne_isCompact.isClosed).2
  intro ε hε
  obtain ⟨y, ⟨b, hb, hy⟩, hxy⟩ := UpperTreeIntoDigitsOne.tree_approx ka_bound
    UpperTreeIntoDigitsOne.path_backward UpperTreeIntoDigitsOne.sem_nonempty
    [1] 3 (node_mesh [1] 3) x hx ε hε
  refine ⟨y, ⟨cfValue b, ⟨b, hb.1, hb.2, rfl⟩, ?_⟩, hxy⟩
  simpa [prefixEval] using hy.symm
