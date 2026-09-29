-- Prove2me | solution 1 for Freiman.section14_parameter_state
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T19:33:08.564854+00:00
-- url     : https://prove2.me/submissions/7fdfdf29-2f9b-4919-b60f-fb171af5fbff

import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Data.List.Infix

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Freiman

namespace M7Last

instance lowerEndsDec (w s : List ℕ+) : Decidable (lowerEnds w s) := by
  unfold lowerEnds; infer_instance

lemma cd_aux (w : List ℕ+) : ∀ c d : ℕ, c ≤ d → 1 ≤ d →
    (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) (c,d)).1 ≤
      (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) (c,d)).2 ∧
    1 ≤ (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) (c,d)).2 := by
  induction w with
  | nil => intro c d h1 h2; exact ⟨h1, h2⟩
  | cons a t ih =>
      intro c d h1 h2
      have ha : 1 ≤ (a : ℕ) := a.one_le
      refine ih d (c + (a:ℕ)*d) ?_ ?_
      · calc d = 1*d := by ring
          _ ≤ (a:ℕ)*d := Nat.mul_le_mul_right d ha
          _ ≤ c + (a:ℕ)*d := Nat.le_add_left _ _
      · calc (1:ℕ) = 1*1 := by norm_num
          _ ≤ (a:ℕ)*d := Nat.mul_le_mul ha h2
          _ ≤ c + (a:ℕ)*d := Nat.le_add_left _ _

lemma cd_le (w : List ℕ+) : (lowerCD w).1 ≤ (lowerCD w).2 ∧ 1 ≤ (lowerCD w).2 :=
  cd_aux w 0 1 (Nat.zero_le 1) (le_refl 1)

lemma cd_app (v : List ℕ+) (a : ℕ+) :
    lowerCD (v ++ [a]) = ((lowerCD v).2, (lowerCD v).1 + (a:ℕ) * (lowerCD v).2) := by
  simp [lowerCD, List.foldl_append]

lemma ratio_nonneg (w : List ℕ+) : 0 ≤ lowerRatio w := by
  rw [lowerRatio]; positivity

lemma ratio_le_one (w : List ℕ+) : lowerRatio w ≤ 1 := by
  obtain ⟨h1, h2⟩ := cd_le w
  have hd : (0:ℝ) < ((lowerCD w).2 : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h2
  rw [lowerRatio, div_le_one hd]
  exact_mod_cast h1

lemma ratio_nil : lowerRatio ([] : List ℕ+) = 0 := by
  simp [lowerRatio, lowerCD]

lemma ratio_append (v : List ℕ+) (a : ℕ+) :
    lowerRatio (v ++ [a]) = 1 / (((a:ℕ):ℝ) + lowerRatio v) := by
  obtain ⟨h1, h2⟩ := cd_le v
  have hd : (0:ℝ) < ((lowerCD v).2 : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h2
  have hc : (0:ℝ) ≤ ((lowerCD v).1 : ℝ) := Nat.cast_nonneg _
  have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.one_le
  have hden : (0:ℝ) < ((lowerCD v).1 : ℝ) + ((a:ℕ):ℝ) * ((lowerCD v).2 : ℝ) := by nlinarith
  have hden2 : (0:ℝ) < ((a:ℕ):ℝ) + ((lowerCD v).1 : ℝ) / ((lowerCD v).2 : ℝ) := by
    have : (0:ℝ) ≤ ((lowerCD v).1 : ℝ) / ((lowerCD v).2 : ℝ) := by positivity
    linarith
  rw [lowerRatio, lowerRatio, cd_app]
  push_cast
  rw [eq_div_iff (ne_of_gt hden2)]
  field_simp <;> ring

lemma ratio_pos_of_ne_nil (v : List ℕ+) (a : ℕ+) : 0 < lowerRatio (v ++ [a]) := by
  obtain ⟨h1, h2⟩ := cd_le v
  obtain ⟨h3, h4⟩ := cd_le (v ++ [a])
  have hnum : (0:ℝ) < ((lowerCD (v ++ [a])).1 : ℝ) := by
    rw [cd_app]
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h2
  have hden : (0:ℝ) < ((lowerCD (v ++ [a])).2 : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h4
  rw [lowerRatio]
  positivity

lemma suf3 (v : List ℕ+) (b : ℕ+) : lowerEnds (v ++ [b]) [3] ↔ b = 3 := by
  constructor
  · rintro ⟨t, ht⟩
    have h := congrArg List.reverse ht
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.cons.injEq] at h
    exact h.1.symm
  · rintro rfl
    exact ⟨v, rfl⟩

lemma suf31 (v : List ℕ+) (b : ℕ+) :
    lowerEnds (v ++ [b]) [3,1] ↔ (b = 1 ∧ lowerEnds v [3]) := by
  constructor
  · rintro ⟨t, ht⟩
    have h := congrArg List.reverse ht
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.cons.injEq] at h
    refine ⟨h.1.symm, t, ?_⟩
    have h2 := congrArg List.reverse h.2
    simpa using h2
  · rintro ⟨rfl, t, rfl⟩
    exact ⟨t, by simp⟩

lemma sm3 (w c : List ℕ+) (h : lowerEnds w [3] ↔ lowerEnds c [3]) :
    ∀ u : List ℕ+, lowerEnds (w ++ u) [3] ↔ lowerEnds (c ++ u) [3] := by
  intro u
  induction u using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton u' b _ =>
      rw [← List.append_assoc, ← List.append_assoc, suf3, suf3]

lemma sm31 (w c : List ℕ+) (h3 : lowerEnds w [3] ↔ lowerEnds c [3])
    (h : lowerEnds w [3,1] ↔ lowerEnds c [3,1]) :
    ∀ u : List ℕ+, lowerEnds (w ++ u) [3,1] ↔ lowerEnds (c ++ u) [3,1] := by
  intro u
  induction u using List.reverseRecOn with
  | nil => simpa using h
  | append_singleton u' b _ =>
      rw [← List.append_assoc, ← List.append_assoc, suf31, suf31, sm3 w c h3 u']

lemma smatch (w c : List ℕ+) (h3 : lowerEnds w [3] ↔ lowerEnds c [3])
    (h31 : lowerEnds w [3,1] ↔ lowerEnds c [3,1]) : section14SuffixMatches w c :=
  ⟨sm3 w c h3, sm31 w c h3 h31⟩

lemma match_1 (v : List ℕ+) (a : ℕ+) (ha : a = 1) (h3 : ¬ lowerEnds v [3]) :
    section14SuffixMatches (v ++ [a]) [1] := by
  refine smatch _ _ ?_ ?_
  · rw [suf3, ha]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
  · rw [suf31, ha]
    constructor
    · rintro ⟨-, h⟩; exact absurd h h3
    · intro h; exact absurd h (by decide)

lemma match_2 (v : List ℕ+) (a : ℕ+) (ha : a = 2) :
    section14SuffixMatches (v ++ [a]) [2] := by
  refine smatch _ _ ?_ ?_
  · rw [suf3, ha]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
  · rw [suf31, ha]
    constructor
    · rintro ⟨h, -⟩; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)

lemma match_3 (v : List ℕ+) (a : ℕ+) (ha : a = 3) :
    section14SuffixMatches (v ++ [a]) [3] := by
  refine smatch _ _ ?_ ?_
  · rw [suf3, ha]
    constructor
    · intro _; decide
    · intro _; rfl
  · rw [suf31, ha]
    constructor
    · rintro ⟨h, -⟩; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)

lemma match_31 (v : List ℕ+) (a : ℕ+) (ha : a = 1) (h3 : lowerEnds v [3]) :
    section14SuffixMatches (v ++ [a]) [3,1] := by
  refine smatch _ _ ?_ ?_
  · rw [suf3, ha]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
  · rw [suf31, ha]
    constructor
    · intro _; decide
    · intro _; exact ⟨rfl, h3⟩


lemma pnat_eq (a n : ℕ+) (h : (a:ℕ) = (n:ℕ)) : a = n := Subtype.ext h

lemma classify (w : List ℕ+) (hlo : (1/4:ℝ) ≤ lowerRatio w) (hhi : lowerRatio w ≤ 4/5)
    (hne : w ≠ [4]) :
    (section14SuffixMatches w [1] ∧ (1/2:ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 4/5)
  ∨ (section14SuffixMatches w [2] ∧ (1/3:ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 1/2)
  ∨ (section14SuffixMatches w [3] ∧ (1/4:ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 1/3)
  ∨ (section14SuffixMatches w [3,1] ∧ (3/4:ℝ) ≤ lowerRatio w ∧ lowerRatio w ≤ 4/5) := by
  induction w using List.reverseRecOn with
  | nil => exfalso; rw [ratio_nil] at hlo; linarith
  | append_singleton v a _ =>
      have hr := ratio_append v a
      have hp0 : 0 ≤ lowerRatio v := ratio_nonneg v
      have hp1 : lowerRatio v ≤ 1 := ratio_le_one v
      have ha1 : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.one_le
      have hden : (0:ℝ) < ((a:ℕ):ℝ) + lowerRatio v := by linarith
      have hale : ((a:ℕ):ℝ) + lowerRatio v ≤ 4 := by
        rw [hr, le_div_iff₀ hden] at hlo; linarith
      have haN : 1 ≤ (a:ℕ) ∧ (a:ℕ) ≤ 4 := by
        refine ⟨a.one_le, ?_⟩
        have : ((a:ℕ):ℝ) ≤ 4 := by linarith
        exact_mod_cast this
      have hcases : (a:ℕ) = 1 ∨ (a:ℕ) = 2 ∨ (a:ℕ) = 3 ∨ (a:ℕ) = 4 := by omega
      rcases hcases with h | h | h | h
      · have ha' : a = 1 := pnat_eq a 1 (by simpa using h)
        have hrv : lowerRatio (v ++ [a]) = 1 / (1 + lowerRatio v) := by rw [hr, h]; norm_num
        have hden' : (0:ℝ) < 1 + lowerRatio v := by linarith
        by_cases h3 : lowerEnds v [3]
        · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, hhi⟩))
          · exact match_31 v a ha' h3
          · obtain ⟨tl, htl⟩ := h3
            have hvp : lowerRatio v ≤ 1/3 := by
              have : lowerRatio v = 1 / (3 + lowerRatio tl) := by
                rw [← htl, ratio_append]; norm_num
              rw [this, div_le_div_iff₀ (by linarith [ratio_nonneg tl]) (by norm_num)]
              linarith [ratio_nonneg tl]
            rw [hrv, le_div_iff₀ hden']; linarith
        · refine Or.inl ⟨?_, ?_, hhi⟩
          · exact match_1 v a ha' h3
          · rw [hrv, le_div_iff₀ hden']; linarith
      · have ha' : a = 2 := pnat_eq a 2 (by simpa using h)
        have hrv : lowerRatio (v ++ [a]) = 1 / (2 + lowerRatio v) := by rw [hr, h]; norm_num
        have hden' : (0:ℝ) < 2 + lowerRatio v := by linarith
        refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
        · exact match_2 v a ha'
        · rw [hrv, le_div_iff₀ hden']; linarith
        · rw [hrv, div_le_iff₀ hden']; linarith
      · have ha' : a = 3 := pnat_eq a 3 (by simpa using h)
        have hrv : lowerRatio (v ++ [a]) = 1 / (3 + lowerRatio v) := by rw [hr, h]; norm_num
        have hden' : (0:ℝ) < 3 + lowerRatio v := by linarith
        refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
        · exact match_3 v a ha'
        · rw [hrv, le_div_iff₀ hden']; linarith
        · rw [hrv, div_le_iff₀ hden']; linarith
      · exfalso
        have hrv : lowerRatio (v ++ [a]) = 1 / (4 + lowerRatio v) := by rw [hr, h]; norm_num
        have hden' : (0:ℝ) < 4 + lowerRatio v := by linarith
        have hz : lowerRatio v = 0 := by
          rw [hrv, le_div_iff₀ hden'] at hlo
          linarith
        have hvnil : v = [] := by
          induction v using List.reverseRecOn with
          | nil => rfl
          | append_singleton v' b _ => exact absurd hz (ne_of_gt (ratio_pos_of_ne_nil v' b))
        exact hne (by rw [hvnil, pnat_eq a 4 (by simpa using h)]; rfl)

end M7Last

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hm : lowerMixed p) : ∃ i : Fin 16, section14Matches p (section14State section14Catalog (i.val+1)) ∧ certRectangleMem (section14State section14Catalog (i.val+1)).rectangle (section14R p) (section14S p) := by
  classical
  obtain ⟨hadm, hgoodp, hcov, hbox⟩ := hs
  have hcores : ∀ c ∈ lowerCores, c.1 ≠ ([] : List ℕ+) ∧ c.1 ≠ [4] ∧
      c.2 ≠ ([] : List ℕ+) ∧ c.2 ≠ [4] := by decide
  have hne4 : p.1 ≠ [4] ∧ p.2 ≠ [4] := by
    obtain ⟨⟨c, hcmem, u, v, hpeq, _hu, _hv⟩, _⟩ := hadm
    obtain ⟨hc1e, hc1f, hc2e, hc2f⟩ := hcores c hcmem
    have hp1 : p.1 = c.1 ++ u := by rw [hpeq]
    have hp2 : p.2 = c.2 ++ v := by rw [hpeq]
    constructor
    · intro hh
      rw [hp1] at hh
      cases hcase : c.1 with
      | nil => exact hc1e hcase
      | cons x tl =>
          rw [hcase] at hh
          simp only [List.cons_append, List.cons.injEq] at hh
          have h2 : tl = [] ∧ u = [] := by simpa using hh.2
          exact hc1f (by rw [hcase, hh.1, h2.1])
    · intro hh
      rw [hp2] at hh
      cases hcase : c.2 with
      | nil => exact hc2e hcase
      | cons x tl =>
          rw [hcase] at hh
          simp only [List.cons_append, List.cons.injEq] at hh
          have h2 : tl = [] ∧ v = [] := by simpa using hh.2
          exact hc2f (by rw [hcase, hh.1, h2.1])
  have hdata : (1/4:ℝ) ≤ lowerRatio (lowerNormalize p).1 ∧
      lowerRatio (lowerNormalize p).1 ≤ 4/5 ∧ (lowerNormalize p).1 ≠ [4] ∧
      (1/4:ℝ) ≤ lowerRatio (lowerNormalize p).2 ∧
      lowerRatio (lowerNormalize p).2 ≤ 4/5 ∧ (lowerNormalize p).2 ≠ [4] := by
    unfold lowerNormalize
    by_cases hw : lowerWidth p.2 ≤ lowerWidth p.1
    · simp only [hw, if_true]
      exact ⟨hbox.1, hbox.2.1, hne4.1, hbox.2.2.1, hbox.2.2.2, hne4.2⟩
    · simp only [hw, if_false]
      exact ⟨hbox.2.2.1, hbox.2.2.2, hne4.2, hbox.1, hbox.2.1, hne4.1⟩
  have hR : section14R p = lowerRatio (lowerNormalize p).1 := rfl
  have hS : section14S p = lowerRatio (lowerNormalize p).2 := rfl
  have side1 := M7Last.classify (lowerNormalize p).1 hdata.1 hdata.2.1 hdata.2.2.1
  have side2 := M7Last.classify (lowerNormalize p).2 hdata.2.2.2.1 hdata.2.2.2.2.1
    hdata.2.2.2.2.2
  have main : ∀ (j : ℕ) (hj : j < 16) (c1 c2 : List ℕ+) (q0 q1 q2 q3 : ℚ),
      (section14State section14Catalog (j+1)).context = ⟨(c1,c2),(false,true)⟩ →
      (section14State section14Catalog (j+1)).rectangle = ⟨q0,q1,q2,q3⟩ →
      section14SuffixMatches (lowerNormalize p).1 c1 →
      section14SuffixMatches (lowerNormalize p).2 c2 →
      (q0:ℝ) ≤ section14R p → section14R p ≤ (q1:ℝ) →
      (q2:ℝ) ≤ section14S p → section14S p ≤ (q3:ℝ) →
      ∃ i : Fin 16, section14Matches p (section14State section14Catalog (i.val+1)) ∧
        certRectangleMem (section14State section14Catalog (i.val+1)).rectangle
          (section14R p) (section14S p) := by
    intro j hj c1 c2 q0 q1 q2 q3 hctx hrect hs1 hs2 b0 b1 b2 b3
    refine ⟨⟨j, hj⟩, ⟨?_, ?_, ?_⟩, ?_⟩
    · show section14SuffixMatches (lowerNormalize p).1
        (section14State section14Catalog (j+1)).context.words.1
      rw [hctx]; exact hs1
    · show section14SuffixMatches (lowerNormalize p).2
        (section14State section14Catalog (j+1)).context.words.2
      rw [hctx]; exact hs2
    · show (section14State section14Catalog (j+1)).context.parity = (false,true)
      rw [hctx]
    · show certRectangleMem (section14State section14Catalog (j+1)).rectangle
        (section14R p) (section14S p)
      rw [hrect]; exact ⟨b0, b1, b2, b3⟩
  rcases side1 with h1|h1|h1|h1
  · rcases side2 with h2|h2|h2|h2
    · exact main 0 (by norm_num) ([1]) ([1]) (1/2) (4/5) (1/2) (4/5) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
    · exact main 1 (by norm_num) ([1]) ([2]) (1/2) (4/5) (1/3) (1/2) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
    · exact main 2 (by norm_num) ([1]) ([3]) (1/2) (4/5) (1/4) (1/3) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
    · exact main 3 (by norm_num) ([1]) ([3,1]) (1/2) (4/5) (3/4) (4/5) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
  · rcases side2 with h2|h2|h2|h2
    · exact main 4 (by norm_num) ([2]) ([1]) (1/3) (1/2) (1/2) (4/5) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
    · exact main 5 (by norm_num) ([2]) ([2]) (1/3) (1/2) (1/3) (1/2) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
    · exact main 6 (by norm_num) ([2]) ([3]) (1/3) (1/2) (1/4) (1/3) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
    · exact main 7 (by norm_num) ([2]) ([3,1]) (1/3) (1/2) (3/4) (4/5) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
  · rcases side2 with h2|h2|h2|h2
    · exact main 8 (by norm_num) ([3]) ([1]) (1/4) (1/3) (1/2) (4/5) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
    · exact main 9 (by norm_num) ([3]) ([2]) (1/4) (1/3) (1/3) (1/2) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
    · exact main 10 (by norm_num) ([3]) ([3]) (1/4) (1/3) (1/4) (1/3) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
    · exact main 11 (by norm_num) ([3]) ([3,1]) (1/4) (1/3) (3/4) (4/5) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
  · rcases side2 with h2|h2|h2|h2
    · exact main 12 (by norm_num) ([3,1]) ([1]) (3/4) (4/5) (1/2) (4/5) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
    · exact main 13 (by norm_num) ([3,1]) ([2]) (3/4) (4/5) (1/3) (1/2) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
    · exact main 14 (by norm_num) ([3,1]) ([3]) (3/4) (4/5) (1/4) (1/3) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
    · exact main 15 (by norm_num) ([3,1]) ([3,1]) (3/4) (4/5) (3/4) (4/5) rfl rfl h1.1 h2.1
        (by rw [hR]; push_cast; linarith [h1.2.1]) (by rw [hR]; push_cast; linarith [h1.2.2])
        (by rw [hS]; push_cast; linarith [h2.2.1]) (by rw [hS]; push_cast; linarith [h2.2.2])
