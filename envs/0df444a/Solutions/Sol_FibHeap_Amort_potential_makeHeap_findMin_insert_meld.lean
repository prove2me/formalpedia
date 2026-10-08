-- Prove2me | solution 1 for FibHeap.Amort.potential_makeHeap_findMin_insert_meld
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:53:57.611988+00:00
-- url     : https://prove2.me/submissions/f696f3d9-5096-4955-892a-1a3ec4dc73fc

import Mathlib
import Definitions.Def_FibHeap_Amort_Model



namespace FibHeap.Amort
open FTree

def hpot (r : Heap) : ℕ := r.length + 2 * markedNonroot r

theorem potential_eq (s : Coll) : potential s = (s.map hpot).sum := rfl

theorem pot_set (s : Coll) (h : ℕ) (r r' : Heap) (hs : s[h]? = some r) :
    potential (s.set h r') + hpot r = potential s + hpot r' := by
  induction s generalizing h with
  | nil => simp at hs
  | cons a s ih =>
    cases h with
    | zero =>
      simp at hs; subst hs
      simp [potential_eq]; ring
    | succ h =>
      simp at hs
      have := ih h hs
      simp only [potential_eq, List.set_cons_succ, List.map_cons, List.sum_cons] at this ⊢
      omega

theorem hpot_append (r r' : Heap) : hpot (r ++ r') = hpot r + hpot r' := by
  simp [hpot, markedNonroot, List.map_append, List.sum_append]; ring

theorem sum_cost_core (T : ℕ) (s : ℕ → Coll) (op : ℕ → Op) (d : ℕ → StepData)
    (hrun : IsRun T s op d) :
    (∑ t ∈ Finset.range T, (cost (d t) : ℤ)) ≤
      ∑ t ∈ Finset.range T, amortized (d t) (s t) (s (t + 1)) := by
  have h : ∑ t ∈ Finset.range T, amortized (d t) (s t) (s (t + 1)) =
      ∑ t ∈ Finset.range T, (cost (d t) : ℤ) + ((potential (s T) : ℤ) - potential (s 0)) := by
    rw [← Finset.sum_range_sub (fun t => (potential (s t) : ℤ)), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    simp [amortized]; ring
  rw [h, hrun.1]
  have h0 : potential ([] : Coll) = 0 := rfl
  rw [h0]
  have := Int.natCast_nonneg (potential (s T))
  push_cast
  linarith

theorem pot_basic_core (s s' : Coll) (op : Op) (d : StepData)
    (hstep : Step s op s' d) :
    ((op = .makeHeap ∨ (∃ h, op = .findMin h) ∨ (∃ h₁ h₂, op = .meld h₁ h₂)) →
        potential s' = potential s) ∧
      (∀ (i : ℕ) (k : ℝ) (h : ℕ), op = .insert i k h →
        potential s' = potential s + 1) := by
  cases hstep
  case makeHeap => simp [potential, markedNonroot]
  case findMin => simp
  case insert r i k h hs _ =>
    refine ⟨by simp, ?_⟩
    intro i' k' h' he
    have := pot_set s h r (r ++ [.node i k false []]) hs
    rw [hpot_append] at this
    have e : hpot [FTree.node i k false []] = 1 := by
      simp [hpot, markedNonroot, FTree.children]
    omega
  case meld r1 r2 h1 h2 hs1 hs2 hne =>
    refine ⟨?_, by simp⟩
    intro _
    have a1 := pot_set s h1 r1 (r1 ++ r2) hs1
    have hs2' : (s.set h1 (r1 ++ r2))[h2]? = some r2 := by
      rw [List.getElem?_set_ne hne]; exact hs2
    have a2 := pot_set (s.set h1 (r1 ++ r2)) h2 r2 [] hs2'
    rw [hpot_append] at a1
    have : hpot ([] : Heap) = 0 := by simp [hpot, markedNonroot]
    omega
  all_goals simp

end FibHeap.Amort

open FibHeap.Amort


theorem solution (s s' : Coll) (op : Op) (d : StepData)
    (hstep : Step s op s' d) :
    ((op = .makeHeap ∨ (∃ h, op = .findMin h) ∨ (∃ h₁ h₂, op = .meld h₁ h₂)) →
        potential s' = potential s) ∧
      (∀ (i : ℕ) (k : ℝ) (h : ℕ), op = .insert i k h →
        potential s' = potential s + 1) := by
  exact pot_basic_core s s' op d hstep
