-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_domain_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T00:19:39.729727+00:00
-- url     : https://prove2.me/submissions/0298fd5a-80ac-48af-9c19-36cc095083a8

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic

open Freiman

private theorem cd_bounds : ∀ (w : List ℕ+) (z : ℕ × ℕ), z.1 ≤ z.2 → 1 ≤ z.2 →
    (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) z).1
        ≤ (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) z).2 ∧
      1 ≤ (w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) z).2 := by
  intro w
  induction w with
  | nil => intro z h1 h2; exact ⟨h1, h2⟩
  | cons a t ih =>
    intro z h1 h2
    have ha : 1 ≤ (a : ℕ) := a.property
    have key : z.2 ≤ (a:ℕ) * z.2 := by
      calc z.2 = 1 * z.2 := by ring
        _ ≤ (a:ℕ) * z.2 := Nat.mul_le_mul_right _ ha
    refine ih _ ?_ ?_ <;> simp only <;> omega

private theorem cd_le (w : List ℕ+) : (lowerCD w).1 ≤ (lowerCD w).2 := by
  unfold lowerCD; exact (cd_bounds w (0,1) (by norm_num) (by norm_num)).1

private theorem cd_pos (w : List ℕ+) : 1 ≤ (lowerCD w).2 := by
  unfold lowerCD; exact (cd_bounds w (0,1) (by norm_num) (by norm_num)).2

private theorem cd_den_posR (w : List ℕ+) : (0:ℝ) < ((lowerCD w).2 : ℝ) := by
  have := cd_pos w; exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one this

private theorem ratio_nonneg (w : List ℕ+) : 0 ≤ lowerRatio w := by
  unfold lowerRatio; positivity

private theorem ratio_le_one (w : List ℕ+) : lowerRatio w ≤ 1 := by
  unfold lowerRatio
  rw [div_le_one (cd_den_posR w)]
  exact_mod_cast cd_le w

/-- Appending one letter is a Möbius step on the ratio:
`ratio (u ++ [a]) = 1 / (a + ratio u)`. -/
private theorem ratio_append_one (u : List ℕ+) (a : ℕ+) :
    lowerRatio (u ++ [a]) = 1 / ((a : ℕ) + lowerRatio u) := by
  have hcd : lowerCD (u ++ [a]) = ((lowerCD u).2, (lowerCD u).1 + (a:ℕ) * (lowerCD u).2) := by
    simp [lowerCD, List.foldl_append]
  have hd := cd_den_posR u
  have ha : (0:ℝ) < ((a:ℕ):ℝ) := by
    have : 1 ≤ (a:ℕ) := a.property
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one this
  unfold lowerRatio
  rw [hcd]
  push_cast
  rw [eq_div_iff (by positivity)]
  field_simp
  ring

private theorem ratio_suffix_3 (u : List ℕ+) :
    1/4 ≤ lowerRatio (u ++ [3]) ∧ lowerRatio (u ++ [3]) ≤ 1/3 := by
  have h0 := ratio_nonneg u
  have h1 := ratio_le_one u
  rw [ratio_append_one]
  have hc : (((3 : ℕ+) : ℕ) : ℝ) = 3 := by norm_num
  rw [hc]
  constructor
  · rw [le_div_iff₀ (by linarith)]; linarith
  · rw [div_le_iff₀ (by linarith)]; linarith

/-- One Möbius step, with explicit interval arithmetic. -/
private theorem step_bounds (u : List ℕ+) (a : ℕ+) (A lo hi : ℝ)
    (hA : (((a : ℕ)) : ℝ) = A) (hApos : 0 < A) (hlo : 0 ≤ lo)
    (h1 : lo ≤ lowerRatio u) (h2 : lowerRatio u ≤ hi) :
    1/(A+hi) ≤ lowerRatio (u ++ [a]) ∧ lowerRatio (u ++ [a]) ≤ 1/(A+lo) := by
  rw [ratio_append_one, hA]
  exact ⟨one_div_le_one_div_of_le (by linarith) (by linarith),
    one_div_le_one_div_of_le (by linarith) (by linarith)⟩

private theorem ratio_suffix_1 (u : List ℕ+) :
    1/2 ≤ lowerRatio (u ++ [1]) ∧ lowerRatio (u ++ [1]) ≤ 1 := by
  obtain ⟨a, b⟩ := step_bounds u 1 1 0 1 (by norm_num) (by norm_num) (by norm_num)
    (ratio_nonneg u) (ratio_le_one u)
  norm_num at a b ⊢
  exact ⟨a, b⟩

private theorem ratio_suffix_2 (u : List ℕ+) :
    1/3 ≤ lowerRatio (u ++ [2]) ∧ lowerRatio (u ++ [2]) ≤ 1/2 := by
  obtain ⟨a, b⟩ := step_bounds u 2 2 0 1 (by norm_num) (by norm_num) (by norm_num)
    (ratio_nonneg u) (ratio_le_one u)
  norm_num at a b ⊢
  exact ⟨a, b⟩

private theorem ratio_suffix_31 (u : List ℕ+) :
    3/4 ≤ lowerRatio (u ++ [3,1]) ∧ lowerRatio (u ++ [3,1]) ≤ 4/5 := by
  obtain ⟨h1, h2⟩ := ratio_suffix_3 u
  obtain ⟨a, b⟩ := step_bounds (u ++ [3]) 1 1 (1/4) (1/3) (by norm_num) (by norm_num)
    (by norm_num) h1 h2
  have he : (u ++ [3]) ++ [1] = u ++ [3,1] := by simp
  rw [he] at a b
  norm_num at a b ⊢
  exact ⟨a, b⟩

private theorem ratio_suffix_313 (u : List ℕ+) :
    5/19 ≤ lowerRatio (u ++ [3,1,3]) ∧ lowerRatio (u ++ [3,1,3]) ≤ 4/15 := by
  obtain ⟨h1, h2⟩ := ratio_suffix_31 u
  obtain ⟨a, b⟩ := step_bounds (u ++ [3,1]) 3 3 (3/4) (4/5) (by norm_num) (by norm_num)
    (by norm_num) h1 h2
  have he : (u ++ [3,1]) ++ [3] = u ++ [3,1,3] := by simp
  rw [he] at a b
  norm_num at a b ⊢
  exact ⟨a, b⟩

private theorem ratio_suffix_3131 (u : List ℕ+) :
    15/19 ≤ lowerRatio (u ++ [3,1,3,1]) ∧ lowerRatio (u ++ [3,1,3,1]) ≤ 19/24 := by
  obtain ⟨h1, h2⟩ := ratio_suffix_313 u
  obtain ⟨a, b⟩ := step_bounds (u ++ [3,1,3]) 1 1 (5/19) (4/15) (by norm_num) (by norm_num)
    (by norm_num) h1 h2
  have he : (u ++ [3,1,3]) ++ [1] = u ++ [3,1,3,1] := by simp
  rw [he] at a b
  norm_num at a b ⊢
  exact ⟨a, b⟩

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (C : LowerEarlyTerminalCatalog)
    (hc : C ∈ [lowerEarlyTerminalEarly3,lowerEarlyTerminalState1,lowerEarlyTerminalState2,lowerEarlyTerminalTerminal3])
    (he : lowerEnds (lowerNormalize p).1 C.leftContext) :
    certRectangleMem C.rectangle (lowerEarlyTerminalR p) (lowerEarlyTerminalS p) := by
  -- both coordinates of the normalised pair inherit the parameter box
  have hbox := hs.2.2.2
  have hnorm : lowerNormalize p = p ∨ lowerNormalize p = (p.2,p.1) := by
    unfold lowerNormalize
    by_cases hw : lowerWidth p.2 ≤ lowerWidth p.1
    · exact Or.inl (by simp [hw])
    · exact Or.inr (by simp [hw])
  have hup : lowerRatio (lowerNormalize p).1 ≤ 4/5 := by
    rcases hnorm with h | h <;> rw [h]
    · exact hbox.2.1
    · exact hbox.2.2.2
  -- the right word ends with [3,1] on the early domain, pinning the s-interval
  obtain ⟨v, hv⟩ : ∃ v, v ++ [3,1] = (lowerNormalize p).2 := hd.2.2.2.2.1
  have hs2 : 3/4 ≤ lowerRatio (lowerNormalize p).2 ∧ lowerRatio (lowerNormalize p).2 ≤ 4/5 := by
    rw [← hv]; exact ratio_suffix_31 v
  unfold lowerEarlyTerminalR lowerEarlyTerminalS
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp only [lowerEarlyTerminalEarly3, lowerEarlyTerminalState1, lowerEarlyTerminalState2,
      lowerEarlyTerminalTerminal3] at he ⊢ <;>
    obtain ⟨u, hu⟩ := he <;>
    refine ⟨?_, ?_, by norm_num; linarith [hs2.1], by norm_num; linarith [hs2.2]⟩
  all_goals first
    | (rw [← hu]; norm_num; linarith [(ratio_suffix_1 u).1])
    | (rw [← hu]; norm_num; linarith [(ratio_suffix_2 u).1, (ratio_suffix_2 u).2])
    | (rw [← hu]; norm_num; linarith [(ratio_suffix_3 u).1, (ratio_suffix_3 u).2])
    | (norm_num; linarith)
