-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_tie3_structure
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-13T15:48:10.407387+00:00
-- url     : https://prove2.me/submissions/fbc53d20-bdc4-448f-b994-39c306512699

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

namespace M7T3

lemma cd_append (u v : List ℕ+) :
    lowerCD (u ++ v) = v.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) (lowerCD u) := by
  simp [lowerCD, List.foldl_append]

lemma cd_snd_pos (u : List ℕ+) : 0 < (lowerCD u).2 := by
  induction u using List.reverseRecOn with
  | nil => exact Nat.one_pos
  | append_singleton u a ih =>
      rw [cd_append]
      exact Nat.lt_of_lt_of_le (Nat.mul_pos a.property ih) (Nat.le_add_left _ _)

end M7T3

open M7T3

theorem solution (hc : ∀ u v : List ℕ+, lowerWidth u = lowerWidth v → (((lowerCD u).1:ℤ)^2+((lowerCD u).2:ℤ)^2 =
        ((lowerCD v).1:ℤ)^2+((lowerCD v).2:ℤ)^2) ∧
      (4*((lowerCD u).1:ℤ)*(lowerCD u).2-3*((lowerCD u).1:ℤ)^2 =
        4*((lowerCD v).1:ℤ)*(lowerCD v).2-3*((lowerCD v).1:ℤ)^2))
    (ht : ∀ u v : List ℕ+, lowerWidth u = lowerWidth v →
      lowerRatio u = lowerRatio v ∨ lowerRatio v = (4-3*lowerRatio u)/(3+4*lowerRatio u))
    (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l) (he : lowerEarlyTerminalTie3 p l) :
    let w := lowerEarlyTerminalForkPair p l true 2
    (∃ a : ℕ+, ∃ u : List ℕ+, w.1 = a::u ∧ 3 ≤ (a:ℕ)) ∧
    (∃ a : ℕ+, ∃ v : List ℕ+, w.2 = a::v ∧ 3 ≤ (a:ℕ)) ∧
    w.1.length % 2 ≠ w.2.length % 2 ∧ lowerCD w.1 = lowerCD w.2 := by
  obtain ⟨hl, -, hwid⟩ := he
  subst hl
  intro w
  have hw1 : w.1 = (lowerNormalize p).1 ++ [2,2] := rfl
  have hw2 : w.2 = (lowerNormalize p).2 ++ [3,2,2] := rfl
  -- core head facts
  obtain ⟨⟨⟨c, hcmem, uu, vv, hpc, -, -⟩, -⟩, -, -, hbox⟩ := hs
  have hhead : ∀ r ∈ lowerCores, (∃ a : ℕ+, ∃ z : List ℕ+, r.1 = a :: z ∧ 3 ≤ (a:ℕ)) ∧
      (∃ a : ℕ+, ∃ z : List ℕ+, r.2 = a :: z ∧ 3 ≤ (a:ℕ)) := by
    intro r hr
    fin_cases hr <;>
      exact ⟨⟨_, _, rfl, by decide⟩, ⟨_, _, rfl, by decide⟩⟩
  obtain ⟨⟨a1, z1, hc1, ha1⟩, ⟨a2, z2, hc2, ha2⟩⟩ := hhead c hcmem
  have hp1 : p.1 = a1 :: (z1 ++ uu) := by rw [hpc]; simp [hc1]
  have hp2 : p.2 = a2 :: (z2 ++ vv) := by rw [hpc]; simp [hc2]
  have hpar : p.1.length % 2 = p.2.length % 2 := by
    have := hd.1; unfold lowerMixed at this; omega
  have hnorm : lowerNormalize p = p ∨ lowerNormalize p = (p.2, p.1) := by
    by_cases hh : lowerWidth p.2 ≤ lowerWidth p.1
    · left; simp [lowerNormalize, hh]
    · right; simp [lowerNormalize, hh]
  -- head facts for the normalized pair
  have hq : (∃ a : ℕ+, ∃ z : List ℕ+, (lowerNormalize p).1 = a :: z ∧ 3 ≤ (a:ℕ)) ∧
      (∃ a : ℕ+, ∃ z : List ℕ+, (lowerNormalize p).2 = a :: z ∧ 3 ≤ (a:ℕ)) ∧
      (lowerNormalize p).1.length % 2 = (lowerNormalize p).2.length % 2 ∧
      lowerParameterBox (lowerNormalize p) := by
    rcases hnorm with hh | hh <;> rw [hh]
    · exact ⟨⟨a1, _, hp1, ha1⟩, ⟨a2, _, hp2, ha2⟩, hpar, hbox⟩
    · exact ⟨⟨a2, _, hp2, ha2⟩, ⟨a1, _, hp1, ha1⟩, hpar.symm,
        ⟨hbox.2.2.1, hbox.2.2.2, hbox.1, hbox.2.1⟩⟩
  obtain ⟨⟨b1, y1, hb1, hb1'⟩, ⟨b2, y2, hb2, hb2'⟩, hqpar, hqbox⟩ := hq
  -- the three easy conjuncts
  refine ⟨⟨b1, y1 ++ [2,2], by rw [hw1, hb1]; simp, hb1'⟩,
          ⟨b2, y2 ++ [3,2,2], by rw [hw2, hb2]; simp, hb2'⟩, ?_, ?_⟩
  · rw [hw1, hw2]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  -- the continuant identity
  set X := lowerCD (lowerNormalize p).1 with hX
  set Y := lowerCD (lowerNormalize p).2 with hY
  have hD1 : 0 < X.2 := cd_snd_pos _
  have hD2 : 0 < Y.2 := cd_snd_pos _
  have hcd1a : (lowerCD w.1).1 = X.1 + 2*X.2 := by rw [hw1, cd_append]; rfl
  have hcd1b : (lowerCD w.1).2 = 2*X.1 + 5*X.2 := by
    rw [hw1, cd_append]; show X.2 + 2*(X.1 + 2*X.2) = 2*X.1 + 5*X.2; ring
  have hcd2a : (lowerCD w.2).1 = 2*Y.1 + 7*Y.2 := by
    rw [hw2, cd_append]; show Y.2 + 2*(Y.1 + 3*Y.2) = 2*Y.1 + 7*Y.2; ring
  have hcd2b : (lowerCD w.2).2 = 5*Y.1 + 17*Y.2 := by
    rw [hw2, cd_append]
    show (Y.1 + 3*Y.2) + 2*(Y.2 + 2*(Y.1 + 3*Y.2)) = 5*Y.1 + 17*Y.2; ring
  have hXnn : (0:ℝ) ≤ (X.1:ℝ) := Nat.cast_nonneg _
  have hYnn : (0:ℝ) ≤ (Y.1:ℝ) := Nat.cast_nonneg _
  have hXp : (0:ℝ) < (X.2:ℝ) := by exact_mod_cast hD1
  have hYp : (0:ℝ) < (Y.2:ℝ) := by exact_mod_cast hD2
  have hx : (5:ℝ)*(X.1:ℝ) ≤ 4*(X.2:ℝ) := by
    have h := hqbox.2.1
    simp only [lowerRatio, ← hX] at h
    rw [div_le_iff₀ hXp] at h; linarith
  have hr1 : lowerRatio w.1 = ((X.1:ℝ) + 2*(X.2:ℝ)) / (2*(X.1:ℝ) + 5*(X.2:ℝ)) := by
    simp only [lowerRatio, hcd1a, hcd1b]; push_cast; ring
  have hr2 : lowerRatio w.2 = (2*(Y.1:ℝ) + 7*(Y.2:ℝ)) / (5*(Y.1:ℝ) + 17*(Y.2:ℝ)) := by
    simp only [lowerRatio, hcd2a, hcd2b]; push_cast; ring
  have hden1 : (0:ℝ) < 2*(X.1:ℝ) + 5*(X.2:ℝ) := by linarith
  have hden2 : (0:ℝ) < 5*(Y.1:ℝ) + 17*(Y.2:ℝ) := by linarith
  have hr1hi : lowerRatio w.1 ≤ 43/100 := by
    rw [hr1, div_le_iff₀ hden1]; linarith
  have hr1lo : (2:ℝ)/5 ≤ lowerRatio w.1 := by
    rw [hr1, le_div_iff₀ hden1]; linarith
  have hr2hi : lowerRatio w.2 ≤ 42/100 := by
    rw [hr2, div_le_iff₀ hden2]; linarith
  have hr2lo : (0:ℝ) ≤ lowerRatio w.2 := by
    rw [hr2]; positivity
  rcases ht w.1 w.2 hwid with heq | hrot
  · -- equal ratios: the circle invariant forces the continuants to agree
    have hB1 : (0:ℝ) < ((lowerCD w.1).2 : ℝ) := by rw [hcd1b]; push_cast; linarith
    have hB2 : (0:ℝ) < ((lowerCD w.2).2 : ℝ) := by rw [hcd2b]; push_cast; linarith
    have hcrR : (((lowerCD w.1).1 : ℝ)) * ((lowerCD w.2).2 : ℝ)
        = ((lowerCD w.2).1 : ℝ) * ((lowerCD w.1).2 : ℝ) := by
      simp only [lowerRatio] at heq
      field_simp at heq
      linarith [heq]
    have hcrN : (lowerCD w.1).1 * (lowerCD w.2).2 = (lowerCD w.2).1 * (lowerCD w.1).2 := by
      exact_mod_cast hcrR
    have hcrZ : ((lowerCD w.1).1 : ℤ) * ((lowerCD w.2).2 : ℤ)
        = ((lowerCD w.2).1 : ℤ) * ((lowerCD w.1).2 : ℤ) := by exact_mod_cast hcrN
    have hsq := (hc w.1 w.2 hwid).1
    have hB2Z : (0:ℤ) < ((lowerCD w.2).2 : ℤ) := by exact_mod_cast hB2
    have hB1Z : (0:ℤ) < ((lowerCD w.1).2 : ℤ) := by exact_mod_cast hB1
    have key : (((lowerCD w.1).2 : ℤ)^2 - ((lowerCD w.2).2 : ℤ)^2)
        * (((lowerCD w.2).1 : ℤ)^2 + ((lowerCD w.2).2 : ℤ)^2) = 0 := by
      linear_combination (((lowerCD w.2).2 : ℤ))^2 * hsq
        - (((lowerCD w.2).1 : ℤ) * ((lowerCD w.1).2 : ℤ)
           + ((lowerCD w.1).1 : ℤ) * ((lowerCD w.2).2 : ℤ)) * hcrZ
    have hNpos : (0:ℤ) < ((lowerCD w.2).1 : ℤ)^2 + ((lowerCD w.2).2 : ℤ)^2 := by positivity
    have hBsq : ((lowerCD w.1).2 : ℤ)^2 = ((lowerCD w.2).2 : ℤ)^2 := by
      rcases mul_eq_zero.mp key with h | h
      · linarith
      · exact absurd h (ne_of_gt hNpos)
    have hBeq : ((lowerCD w.1).2 : ℤ) = ((lowerCD w.2).2 : ℤ) := by
      have h0 : (((lowerCD w.1).2 : ℤ) - ((lowerCD w.2).2 : ℤ))
          * (((lowerCD w.1).2 : ℤ) + ((lowerCD w.2).2 : ℤ)) = 0 := by linarith [hBsq]
      rcases mul_eq_zero.mp h0 with h | h
      · linarith
      · linarith
    have hAeq : ((lowerCD w.1).1 : ℤ) = ((lowerCD w.2).1 : ℤ) := by
      have : ((lowerCD w.1).1 : ℤ) * ((lowerCD w.2).2 : ℤ)
          = ((lowerCD w.2).1 : ℤ) * ((lowerCD w.2).2 : ℤ) := by rw [hcrZ, hBeq]
      exact mul_right_cancel₀ (ne_of_gt hB2Z) this
    have hA : (lowerCD w.1).1 = (lowerCD w.2).1 := by exact_mod_cast hAeq
    have hB : (lowerCD w.1).2 = (lowerCD w.2).2 := by exact_mod_cast hBeq
    exact Prod.ext hA hB
  · -- rotated ratios: impossible on the parameter box
    exfalso
    have hpos : (0:ℝ) < 3 + 4 * lowerRatio w.1 := by linarith
    rw [eq_div_iff (ne_of_gt hpos)] at hrot
    nlinarith [hr1lo, hr1hi, hr2hi, hr2lo]
