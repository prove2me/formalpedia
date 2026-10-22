-- Prove2me | solution 1 for CondC.disc_liquid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T17:40:43.790647+00:00
-- url     : https://prove2.me/submissions/eefe837a-eb5e-40a9-b969-b2d74dbc4643

import Mathlib
import Definitions.Def_CondC_liq
import Definitions.Def_CondC_geo

open CondC

section g72cc
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
variable {V : Type} [AddCommGroup V] [Module ℂ V]

def g72cc_Z (a : ℕ → V) : Prop := ∃ N : ℕ, ∀ n ≥ N, a n = 0

theorem g72cc_Z_add (a b : ℕ → V) (ha : g72cc_Z a) (hb : g72cc_Z b) :
    g72cc_Z (fun n => a n + b n) := by
  obtain ⟨N, hN⟩ := ha; obtain ⟨M, hM⟩ := hb
  exact ⟨max N M, fun n hn => by simp [hN n (le_of_max_le_left hn), hM n (le_of_max_le_right hn)]⟩

theorem g72cc_Z_sub (a b : ℕ → V) (ha : g72cc_Z a) (hb : g72cc_Z b) :
    g72cc_Z (fun n => a n - b n) := by
  obtain ⟨N, hN⟩ := ha; obtain ⟨M, hM⟩ := hb
  exact ⟨max N M, fun n hn => by simp [hN n (le_of_max_le_left hn), hM n (le_of_max_le_right hn)]⟩

theorem g72cc_Z_smul (k : ℂ) (a : ℕ → V) (ha : g72cc_Z a) : g72cc_Z (fun n => k • a n) := by
  obtain ⟨N, hN⟩ := ha
  exact ⟨N, fun n hn => by simp [hN n hn]⟩

theorem g72cc_sum_eq (a : ℕ → V) (N M : ℕ) (hN : ∀ n ≥ N, a n = 0) (hM : ∀ n ≥ M, a n = 0) :
    ∑ n ∈ Finset.range N, a n = ∑ n ∈ Finset.range M, a n := by
  wlog h : N ≤ M generalizing N M
  · exact (this M N hM hN (by omega)).symm
  rw [← Finset.sum_range_add_sum_Ico _ h]
  rw [Finset.sum_eq_zero (fun n hn => hN n (Finset.mem_Ico.1 hn).1), add_zero]

open Classical in
noncomputable def g72cc_int (a : ℕ → V) (h : g72cc_Z a) : V :=
  ∑ n ∈ Finset.range (Nat.find h), a n

theorem g72cc_int_eq (a : ℕ → V) (h : g72cc_Z a) (N : ℕ) (hN : ∀ n ≥ N, a n = 0) :
    g72cc_int a h = ∑ n ∈ Finset.range N, a n := by
  classical
  unfold g72cc_int
  exact g72cc_sum_eq a _ _ (Nat.find_spec h) hN

theorem g72cc_uniq (I : ∀ a : ℕ → V, g72cc_Z a → V)
    (hD : ∀ (v : V) (n : ℕ) (h : g72cc_Z (DiracV v n)), I (DiracV v n) h = v)
    (hA : ∀ (a b : ℕ → V) (ha : g72cc_Z a) (hb : g72cc_Z b),
      I (fun n => a n + b n) (g72cc_Z_add a b ha hb) = I a ha + I b hb) :
    ∀ (N : ℕ) (a : ℕ → V) (hN : ∀ n ≥ N, a n = 0) (ha : g72cc_Z a),
      I a ha = ∑ n ∈ Finset.range N, a n := by
  have congrI : ∀ (a b : ℕ → V) (hab : a = b) (ha : g72cc_Z a) (hb : g72cc_Z b), I a ha = I b hb := by
    intro a b hab ha hb; subst hab; rfl
  intro N
  induction N with
  | zero =>
    intro a hN ha
    have h0 : a = 0 := funext fun n => hN n (Nat.zero_le n)
    have := hA a a ha ha
    rw [congrI (fun n => a n + a n) a (by funext n; simp [h0]) _ ha] at this
    simp only [Finset.range_zero, Finset.sum_empty]
    have : I a ha + I a ha = I a ha + 0 := by rw [← this, add_zero]
    exact add_left_cancel this
  | succ N ih =>
    intro a hN ha
    let a' : ℕ → V := fun n => if n = N then 0 else a n
    have ha' : ∀ n ≥ N, a' n = 0 := by
      intro n hn; by_cases h : n = N
      · simp [a', h]
      · simp only [a', h, if_false]; exact hN n (by omega)
    have hZ' : g72cc_Z a' := ⟨N, ha'⟩
    have hZD : g72cc_Z (DiracV (a N) N) := ⟨N + 1, fun n hn => by simp [DiracV]; omega⟩
    have hsplit : (fun n => a' n + DiracV (a N) N n) = a := by
      funext n; by_cases h : n = N
      · subst h; simp [a', DiracV]
      · simp [a', DiracV, h]
    have := hA a' (DiracV (a N) N) hZ' hZD
    rw [congrI _ a hsplit _ ha, ih a' ha' hZ', hD] at this
    rw [this, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn; have : n ≠ N := by simp at hn; omega
    simp [a', this]

end g72cc

theorem solution : ∀ (p r : ℝ), 0 < p → p ≤ 1 → 0 < r →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V],
      DiscAlgebraData r V → IsPLiquid p V := by
  intro p r _ _ _ V _ _ _
  refine ⟨{
    summable := fun _ => True
    dirac_summable := fun _ _ => trivial
    summable_add := fun _ _ _ _ => trivial
    summable_sub := fun _ _ _ _ => trivial
    summable_smul := fun _ _ _ => trivial
    nullseq := g72cc_Z
    null_add := g72cc_Z_add
    null_smul := g72cc_Z_smul
    null_eventually_zero := fun _ h => h
    integrate := g72cc_int
    integrate_dirac := ?_
    integrate_add := ?_
    integrate_smul := ?_
    integrate_unique := ?_ }⟩
  · intro v n h
    rw [g72cc_int_eq _ h (n + 1) (fun m hm => by simp [DiracV]; omega)]
    rw [Finset.sum_eq_single n (fun m _ hm => by simp [DiracV, hm]) (fun h => by simp at h)]
    simp [DiracV]
  · intro a b ha hb
    obtain ⟨N, hN⟩ := id ha; obtain ⟨M, hM⟩ := id hb
    have hN' : ∀ n ≥ max N M, a n = 0 := fun n hn => hN n (le_of_max_le_left hn)
    have hM' : ∀ n ≥ max N M, b n = 0 := fun n hn => hM n (le_of_max_le_right hn)
    rw [g72cc_int_eq _ _ (max N M) (fun n hn => by simp [hN' n hn, hM' n hn]),
      g72cc_int_eq _ _ _ hN', g72cc_int_eq _ _ _ hM', Finset.sum_add_distrib]
  · intro k a ha
    obtain ⟨N, hN⟩ := id ha
    rw [g72cc_int_eq _ _ N (fun n hn => by simp [hN n hn]), g72cc_int_eq _ _ _ hN, Finset.smul_sum]
  · intro I hD hA _ a ha
    obtain ⟨N, hN⟩ := id ha
    rw [g72cc_uniq I hD hA N a hN ha, g72cc_int_eq _ _ _ hN]
