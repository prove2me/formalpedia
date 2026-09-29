-- Prove2me | solution 1 for Freiman.trunk_endpoint_strict_mixed
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T08:04:47.306624+00:00
-- url     : https://prove2.me/submissions/763793d5-016f-4499-baa6-fa5668214e1f

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

def SmallT : List (List ℕ+) := [[3],[2,1,3]]
def BigT : List (List ℕ+) := [[1,3],[1,2,1,3]]
noncomputable def fam (n : ℕ) (u : Bool) : List (List ℕ+) :=
  if (n % 2 = 0) = (!u) then SmallT else BigT

lemma suffix_mem (w : List ℕ+) (u short : Bool) :
    lowerEndpointSuffix w u short ∈ fam w.length u := by
  unfold lowerEndpointSuffix fam SmallT BigT
  split_ifs <;> simp

lemma pe_append (a b : List ℕ+) (x : ℝ) :
    prefixEval (a ++ b) x = prefixEval a (prefixEval b x) := by
  induction a with
  | nil => rfl
  | cons h t ih => simp [prefixEval, ih]

lemma pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a t ih =>
    simp only [prefixEval]
    have : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    apply div_nonneg zero_le_one
    linarith

lemma pe_mono (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x < y) :
    (w.length % 2 = 0 → prefixEval w x < prefixEval w y) ∧
    (w.length % 2 = 1 → prefixEval w y < prefixEval w x) := by
  induction w with
  | nil => exact ⟨fun _ => hxy, fun h => by simp at h⟩
  | cons a t ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have px := pe_nonneg t x hx
    have py := pe_nonneg t y hy
    constructor
    · intro he
      have ho : t.length % 2 = 1 := by simp at he; omega
      have := ih.2 ho
      simp only [prefixEval]
      apply one_div_lt_one_div_of_lt <;> linarith
    · intro ho
      have he : t.length % 2 = 0 := by simp at ho; omega
      have := ih.1 he
      simp only [prefixEval]
      apply one_div_lt_one_div_of_lt <;> linarith

lemma tau_pos : 0 < lowerTau := by
  unfold lowerTau
  rw [sub_pos, show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma v3_bounds : 0 ≤ prefixEval [3] lowerTau ∧ prefixEval [3] lowerTau ≤ 1/3 := by
  have hτ := tau_pos
  have e : prefixEval [3] lowerTau = 1/(3 + lowerTau) := by simp [prefixEval]
  rw [e]
  constructor
  · apply div_nonneg zero_le_one; linarith
  · rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith

lemma v13_bounds : 3/4 ≤ prefixEval [1,3] lowerTau ∧ prefixEval [1,3] lowerTau ≤ 1 := by
  have h := v3_bounds
  have e : prefixEval [1,3] lowerTau = 1/(1 + prefixEval [3] lowerTau) := by simp [prefixEval]
  rw [e]
  constructor
  · calc (3/4:ℝ) = 1/(1+1/3) := by norm_num
      _ ≤ 1/(1 + prefixEval [3] lowerTau) := one_div_le_one_div_of_le (by linarith) (by linarith)
  · rw [div_le_iff₀ (by linarith)]; linarith

lemma v213_bounds : 0 ≤ prefixEval [2,1,3] lowerTau ∧ prefixEval [2,1,3] lowerTau ≤ 4/11 := by
  have h := v13_bounds
  have e : prefixEval [2,1,3] lowerTau = 1/(2 + prefixEval [1,3] lowerTau) := by simp [prefixEval]
  rw [e]
  constructor
  · apply div_nonneg zero_le_one; linarith
  · calc 1/(2 + prefixEval [1,3] lowerTau) ≤ 1/(2 + 3/4) :=
          one_div_le_one_div_of_le (by norm_num) (by linarith)
      _ = 4/11 := by norm_num

lemma v1213_bounds : 11/15 ≤ prefixEval [1,2,1,3] lowerTau := by
  have h := v213_bounds
  have e : prefixEval [1,2,1,3] lowerTau = 1/(1 + prefixEval [2,1,3] lowerTau) := by simp [prefixEval]
  rw [e]
  calc (11/15:ℝ) = 1/(1+4/11) := by norm_num
    _ ≤ 1/(1 + prefixEval [2,1,3] lowerTau) := one_div_le_one_div_of_le (by linarith) (by linarith)

lemma small_bound (t : List ℕ+) (ht : t ∈ SmallT) :
    0 ≤ prefixEval t lowerTau ∧ prefixEval t lowerTau ≤ 4/11 := by
  simp only [SmallT, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact ⟨v3_bounds.1, by linarith [v3_bounds.2]⟩
  · exact v213_bounds

lemma big_bound (t : List ℕ+) (ht : t ∈ BigT) : 11/15 ≤ prefixEval t lowerTau := by
  simp only [BigT, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · linarith [v13_bounds.1]
  · exact v1213_bounds

lemma equal_shape (p : LowerPair) (u : Bool) : ∃ t1 t2, lowerEqualWords p u = (p.1 ++ t1, p.2 ++ t2) ∧
    t1 ∈ fam p.1.length u ∧ t2 ∈ fam p.2.length u := by
  unfold lowerEqualWords lowerNormalize
  by_cases hc : lowerWidth p.2 ≤ lowerWidth p.1
  · simp only [hc, ↓reduceIte]
    exact ⟨_, _, rfl, suffix_mem _ _ _, suffix_mem _ _ _⟩
  · simp only [hc, ↓reduceIte]
    exact ⟨_, _, rfl, suffix_mem _ _ _, suffix_mem _ _ _⟩

lemma natural_shape (p : LowerPair) (u : Bool) : ∃ t1 t2, lowerNaturalWords p u = (p.1 ++ t1, p.2 ++ t2) ∧
    t1 ∈ fam p.1.length u ∧ t2 ∈ fam p.2.length u :=
  ⟨_, _, rfl, suffix_mem _ _ _, suffix_mem _ _ _⟩

lemma virt_mem (n : ℕ) (u : Bool) (hu : u = decide (n % 2 = 0)) (t : List ℕ+)
    (ht : t ∈ fam (n+1) u) : 1 :: t ∈ fam n u := by
  subst hu
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h' : (n+1) % 2 = 1 := by omega
    simp [fam, SmallT, BigT, h, h'] at ht ⊢
    rcases ht with rfl | rfl <;> simp
  · have h' : (n+1) % 2 = 0 := by omega
    simp [fam, SmallT, BigT, h, h'] at ht ⊢
    rcases ht with rfl | rfl <;> simp

lemma words_shape (p : LowerPair) (u : Bool) : ∃ t1 t2, lowerEndpointWords p u = (p.1 ++ t1, p.2 ++ t2) ∧
    t1 ∈ fam p.1.length u ∧ t2 ∈ fam p.2.length u := by
  unfold lowerEndpointWords
  by_cases hpar : p.1.length % 2 = p.2.length % 2
  · rw [if_pos hpar]
    exact equal_shape p u
  · rw [if_neg hpar]
    by_cases hlw : lowerWidth p.2 ≤ lowerWidth p.1
    · simp only [hlw, ↓reduceIte]
      by_cases hu : u = decide (p.1.length % 2 = 0)
      · rw [if_pos hu]
        obtain ⟨t1, t2, he, h1, h2⟩ := equal_shape (p.1 ++ [1], p.2) u
        refine ⟨1 :: t1, t2, ?_, ?_, h2⟩
        · rw [he]
          simp
        · exact virt_mem p.1.length u hu t1 (by simpa using h1)
      · rw [if_neg hu]
        exact natural_shape p u
    · simp only [hlw, ↓reduceIte]
      by_cases hu : u = decide (p.2.length % 2 = 0)
      · rw [if_pos hu]
        obtain ⟨t1, t2, he, h1, h2⟩ := equal_shape (p.1, p.2 ++ [1]) u
        refine ⟨t1, 1 :: t2, ?_, h1, ?_⟩
        · rw [he]
          simp
        · exact virt_mem p.2.length u hu t2 (by simpa using h2)
      · rw [if_neg hu]
        exact natural_shape p u

lemma side_lt (w : List ℕ+) (a b : List ℕ+) (ha : a ∈ fam w.length false) (hb : b ∈ fam w.length true) :
    prefixEval w (prefixEval a lowerTau) < prefixEval w (prefixEval b lowerTau) := by
  rcases Nat.mod_two_eq_zero_or_one w.length with h | h
  · have ha' : a ∈ SmallT := by simpa [fam, h] using ha
    have hb' : b ∈ BigT := by simpa [fam, h] using hb
    have sa := small_bound a ha'
    have sb := big_bound b hb'
    exact (pe_mono w _ _ sa.1 (by linarith) (by linarith)).1 h
  · have ha' : a ∈ BigT := by simpa [fam, h] using ha
    have hb' : b ∈ SmallT := by simpa [fam, h] using hb
    have sa := big_bound a ha'
    have sb := small_bound b hb'
    exact (pe_mono w _ _ sb.1 (by linarith) (by linarith)).2 h

theorem endpoint_lt (p : LowerPair) : lowerEndpoint p false < lowerEndpoint p true := by
  obtain ⟨a1, a2, ea, ha1, ha2⟩ := words_shape p false
  obtain ⟨b1, b2, eb, hb1, hb2⟩ := words_shape p true
  simp only [lowerEndpoint, ea, eb, pe_append]
  have s1 := side_lt p.1 a1 b1 ha1 hb1
  have s2 := side_lt p.2 a2 b2 ha2 hb2
  linarith

theorem solution (p : LowerPair) (hp : p.1.length % 2 ≠ p.2.length % 2) :
    lowerEndpoint p false < lowerEndpoint p true :=
  endpoint_lt p
