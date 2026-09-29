-- Prove2me | solution 1 for Freiman.upper_digits_into_tree_one
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:07:47.57381+00:00
-- url     : https://prove2.me/submissions/59703bf7-77bf-4552-975a-33cdbfb5a198

import Definitions.Def_Freiman_upperModel
import Theorems.Thm_Freiman_cf_convergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_Freiman_cfValue_prefix
import Definitions.Def_Freiman_gapModel

set_option autoImplicit false
set_option maxHeartbeats 800000
open Freiman

namespace UpperDigitsIntoTreeOneOrder

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
end UpperDigitsIntoTreeOneOrder

namespace UpperDigitsIntoTreeOneKABounds

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
  apply (UpperDigitsIntoTreeOneOrder.gap_comparison UpperDigitsIntoTreeOneOrder.gap_first_difference b period).1
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

end UpperDigitsIntoTreeOneKABounds

open UpperDigitsIntoTreeOneKABounds in
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

namespace UpperDigitsIntoTreeOne

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

end UpperDigitsIntoTreeOne

theorem solution : upperKOne ⊆ upperTreeSet (upperTree [1] 3) := by
  rintro x ⟨y, ⟨b, hb, h3, rfl⟩, rfl⟩
  exact UpperDigitsIntoTreeOne.sem_tree ka_bound [1] 3 (1 / (1 + cfValue b))
    ⟨b, ⟨hb, h3⟩, by norm_num [prefixEval]⟩
