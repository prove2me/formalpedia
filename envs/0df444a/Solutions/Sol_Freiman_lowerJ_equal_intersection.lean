-- Prove2me | solution 1 for Freiman.lowerJ_equal_intersection
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T15:48:18.173991+00:00
-- url     : https://prove2.me/submissions/1bb0401b-5852-4190-b3d5-5f62a5324e5d

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

open Freiman

namespace M7JE

lemma pe_nonneg (w : List ℕ+) : ∀ (x : ℝ), 0 ≤ x → 0 ≤ prefixEval w x := by
  induction w with
  | nil => intro x hx; simpa [prefixEval] using hx
  | cons a w ih =>
      intro x hx
      have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.property
      have h := ih x hx
      have hd : (0:ℝ) < ((a:ℕ):ℝ) + prefixEval w x := by linarith
      simp only [prefixEval]
      positivity

lemma pe_append (u : List ℕ+) : ∀ (v : List ℕ+) (x : ℝ),
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => intro v x; simp [prefixEval]
  | cons a u ih => intro v x; simp only [List.cons_append, prefixEval, ih]

lemma pe_mono_le (w : List ℕ+) : ∀ (x y : ℝ), 0 ≤ x → x ≤ y →
    (w.length % 2 = 0 → prefixEval w x ≤ prefixEval w y) ∧
    (w.length % 2 = 1 → prefixEval w y ≤ prefixEval w x) := by
  induction w with
  | nil => intro x y hx hxy; exact ⟨fun _ => hxy, fun h => by simp at h⟩
  | cons a w ih =>
      intro x y hx hxy
      have hy : (0:ℝ) ≤ y := le_trans hx hxy
      have nx := pe_nonneg w x hx
      have ny := pe_nonneg w y hy
      have ha : (1:ℝ) ≤ ((a:ℕ):ℝ) := by exact_mod_cast a.property
      have dx : (0:ℝ) < ((a:ℕ):ℝ) + prefixEval w x := by linarith
      have dy : (0:ℝ) < ((a:ℕ):ℝ) + prefixEval w y := by linarith
      obtain ⟨he, ho⟩ := ih x y hx hxy
      refine ⟨fun hlen => ?_, fun hlen => ?_⟩
      · have h1 : w.length % 2 = 1 := by simp only [List.length_cons] at hlen; omega
        have hstep := ho h1
        simp only [prefixEval]
        exact one_div_le_one_div_of_le dy (by linarith)
      · have h0 : w.length % 2 = 0 := by simp only [List.length_cons] at hlen; omega
        have hstep := he h0
        simp only [prefixEval]
        exact one_div_le_one_div_of_le dx (by linarith)

end M7JE

open M7JE

theorem solution (hc : (lowerTheta 66-lowerTheta 63)/(lowerTheta 90-lowerTheta 3) < (253/1000:ℝ) ∧ (7/5:ℝ)*(lowerTheta 68-lowerTheta 65)/(lowerTheta 28-lowerTheta 1) < (269/1000:ℝ) ∧ lowerTheta 3 < lowerTheta 30 ∧ lowerTheta 30 < lowerTheta 63 ∧ lowerTheta 63 < lowerTheta 66 ∧ lowerTheta 66 < lowerTheta 90 ∧ lowerTheta 65 < lowerTheta 68 ∧ lowerTheta 1 < lowerTheta 28 ∧ (19/5:ℝ)*(253/1000)*(26/25)<1 ∧ (269/1000:ℝ)<(253/1000)*(133/125)) (p : LowerPair) (ha : lowerAdmissible p) (hp : ¬ lowerMixed p) (hl : lowerEnds p.1 [3]) (hr : lowerEnds p.2 [3]) (hb : lowerParameterBox p) (hwide : lowerWidth p.2 ≤ lowerWidth p.1) (hratio : lowerWidth p.1 < (19/5:ℝ)*lowerWidth p.2) (ht : lowerJEqualContact p) (he : lowerJEqualForkFacts p) : lowerSourceGood p := by
  classical
  have o1 : lowerTheta 3 < lowerTheta 30 := hc.2.2.1
  have o2 : lowerTheta 30 < lowerTheta 63 := hc.2.2.2.1
  have o3 : lowerTheta 63 < lowerTheta 66 := hc.2.2.2.2.1
  have o4 : lowerTheta 66 < lowerTheta 90 := hc.2.2.2.2.2.1
  have htau : (0:ℝ) ≤ lowerTau := by
    have h1 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    unfold lowerTau
    nlinarith
  have t30 : (0:ℝ) ≤ lowerTheta 3 := by
    show (0:ℝ) ≤ prefixEval [3] lowerTau
    exact pe_nonneg _ _ htau
  have t300 : (0:ℝ) ≤ lowerTheta 30 := by linarith
  have t630 : (0:ℝ) ≤ lowerTheta 63 := by linarith
  have t660 : (0:ℝ) ≤ lowerTheta 66 := by linarith
  set q := lowerNormalize p with hqdef
  have hpar : q.1.length % 2 = q.2.length % 2 := by
    unfold lowerMixed at hp
    by_cases hh : lowerWidth p.2 ≤ lowerWidth p.1
    · simp only [hqdef, lowerNormalize, if_pos hh]; omega
    · simp only [hqdef, lowerNormalize, if_neg hh]; omega
  have hact : ∀ x y : ℝ, lowerJActual p x y = 4 + prefixEval q.1 x + prefixEval q.2 y := by
    intro x y; simp only [lowerJActual, ← hqdef]
  obtain ⟨e1, e2, e3, e4⟩ := he
  obtain ⟨hcontact, -⟩ := ht
  by_cases hev : q.1.length % 2 = 0
  · have d1 : (decide (¬ (q.1.length % 2 = 0))) = false := by simp [hev]
    have d2 : (decide (q.1.length % 2 = 0)) = true := by simp [hev]
    rw [d1] at e1 e3
    rw [d2] at e2 e4
    have hev2 : q.2.length % 2 = 0 := by omega
    have m1 := (pe_mono_le q.1 (lowerTheta 30) (lowerTheta 63) t300 (le_of_lt o2)).1 hev
    have m2 := (pe_mono_le q.1 (lowerTheta 63) (lowerTheta 66) t630 (le_of_lt o3)).1 hev
    have m3 := (pe_mono_le q.1 (lowerTheta 66) (lowerTheta 90) t660 (le_of_lt o4)).1 hev
    have m4 := (pe_mono_le q.2 (lowerTheta 3) (lowerTheta 90) t30 (by linarith)).1 hev2
    have hs1 : ((-1:ℝ))^q.1.length = 1 := (Nat.even_iff.mpr hev).neg_one_pow
    rw [hs1, one_mul, hact, hact] at hcontact
    have F1 : lowerSourceEndpoint (lowerChild p ([1],[])) false
        ≤ lowerSourceEndpoint (lowerChild p ([1],[])) true := by
      rw [e1, e2, hact, hact]; linarith
    have F2 : lowerSourceEndpoint (lowerChild p ([2],[])) false
        ≤ lowerSourceEndpoint (lowerChild p ([2],[])) true := by
      rw [e3, e4, hact, hact]; linarith
    have F3 : lowerSourceEndpoint (lowerChild p ([2],[])) false
        ≤ lowerSourceEndpoint (lowerChild p ([1],[])) true := by
      rw [e3, e2, hact, hact]; linarith
    have F4 : lowerSourceEndpoint (lowerChild p ([1],[])) false
        ≤ lowerSourceEndpoint (lowerChild p ([2],[])) true := by
      rw [e1, e4, hact, hact]; linarith
    refine ⟨max (lowerSourceEndpoint (lowerChild p ([1],[])) false)
      (lowerSourceEndpoint (lowerChild p ([2],[])) false), ?_, ?_⟩
    · simp only [lowerSourceCover, Set.mem_Icc]
      exact ⟨le_max_left _ _, max_le F1 F3⟩
    · simp only [lowerSourceCover, Set.mem_Icc]
      exact ⟨le_max_right _ _, max_le F4 F2⟩
  · have hodd : q.1.length % 2 = 1 := by omega
    have d1 : (decide (¬ (q.1.length % 2 = 0))) = true := by simp [hodd]
    have d2 : (decide (q.1.length % 2 = 0)) = false := by simp [hodd]
    rw [d1] at e1 e3
    rw [d2] at e2 e4
    have hodd2 : q.2.length % 2 = 1 := by omega
    have m1 := (pe_mono_le q.1 (lowerTheta 30) (lowerTheta 63) t300 (le_of_lt o2)).2 hodd
    have m2 := (pe_mono_le q.1 (lowerTheta 63) (lowerTheta 66) t630 (le_of_lt o3)).2 hodd
    have m3 := (pe_mono_le q.1 (lowerTheta 66) (lowerTheta 90) t660 (le_of_lt o4)).2 hodd
    have m4 := (pe_mono_le q.2 (lowerTheta 3) (lowerTheta 90) t30 (by linarith)).2 hodd2
    have hs1 : ((-1:ℝ))^q.1.length = -1 := (Nat.odd_iff.mpr hodd).neg_one_pow
    rw [hs1, hact, hact] at hcontact
    have F1 : lowerSourceEndpoint (lowerChild p ([1],[])) false
        ≤ lowerSourceEndpoint (lowerChild p ([1],[])) true := by
      rw [e1, e2, hact, hact]; linarith
    have F2 : lowerSourceEndpoint (lowerChild p ([2],[])) false
        ≤ lowerSourceEndpoint (lowerChild p ([2],[])) true := by
      rw [e3, e4, hact, hact]; linarith
    have F3 : lowerSourceEndpoint (lowerChild p ([2],[])) false
        ≤ lowerSourceEndpoint (lowerChild p ([1],[])) true := by
      rw [e1, e4, hact, hact]; linarith
    have F4 : lowerSourceEndpoint (lowerChild p ([1],[])) false
        ≤ lowerSourceEndpoint (lowerChild p ([2],[])) true := by
      rw [e2, e3, hact, hact]; linarith
    refine ⟨max (lowerSourceEndpoint (lowerChild p ([1],[])) false)
      (lowerSourceEndpoint (lowerChild p ([2],[])) false), ?_, ?_⟩
    · simp only [lowerSourceCover, Set.mem_Icc]
      exact ⟨le_max_left _ _, max_le F1 F3⟩
    · simp only [lowerSourceCover, Set.mem_Icc]
      exact ⟨le_max_right _ _, max_le F4 F2⟩
