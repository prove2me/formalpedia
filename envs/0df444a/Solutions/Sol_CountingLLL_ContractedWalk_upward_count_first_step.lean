-- Prove2me | solution 1 for CountingLLL.ContractedWalk.upward_count_first_step
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:34:54.222666+00:00
-- url     : https://prove2.me/submissions/424123b9-ce1d-43ff-8889-ce362291f65b

import Definitions.Def_CountingLLL_ContractedGF

set_option autoImplicit false
open CountingLLL.ContractedWalk
open scoped BigOperators

private def shift (ω : Tape) : Tape := fun n => ω (n+1)
private def next (ω : Tape) (i : ℕ) : ℕ := if ω 0 then i+2 else i-1

private theorem level_shift (ω : Tape) (i t : ℕ) (hi : 0 < i) :
    level ω i (t+1) = level (shift ω) (next ω i) t := by
  induction t with
  | zero => simp [level, next, hi.ne']
  | succ t ih =>
    change (if level ω i (t+1) = 0 then 0 else if ω (t+1) then level ω i (t+1)+2 else level ω i (t+1)-1) =
      (if level (shift ω) (next ω i) t = 0 then 0 else if (shift ω) t then level (shift ω) (next ω i) t+2 else level (shift ω) (next ω i) t-1)
    rw [ih]
    rfl

private theorem stop_shift (ω : Tape) (i : ℕ) (hi : 0 < i)
    (h : ∃ t, level (shift ω) (next ω i) t = 0) :
    stopTime ω i = 1 + stopTime (shift ω) (next ω i) := by
  classical
  let n := Nat.find h
  have hhit : level (shift ω) (next ω i) n = 0 := Nat.find_spec h
  have hold : ∃ t, level ω i t = 0 := ⟨n+1, by rw [level_shift ω i n hi]; exact hhit⟩
  have hfind : Nat.find hold = n+1 := by
    apply (Nat.find_eq_iff hold).2
    constructor
    · rw [level_shift ω i n hi]; exact hhit
    · intro m hm
      cases m with
      | zero => simp [level, hi.ne']
      | succ m =>
        rw [level_shift ω i m hi]
        exact Nat.find_min h (by dsimp [n] at hm ⊢; omega)
  simp only [stopTime, dif_pos hold, dif_pos h, hfind, n, Nat.add_comm]

private theorem first_step_count (ω : Tape) (i : ℕ) (hi : 0 < i)
    (h : ∃ t, level (shift ω) (next ω i) t = 0) :
    upwardCount ω i = (if ω 0 then 1 else 0) + upwardCount (shift ω) (next ω i) := by
  classical
  unfold upwardCount
  rw [stop_shift ω i hi h]
  rw [show 1 + stopTime (shift ω) (next ω i) = stopTime (shift ω) (next ω i) + 1 by omega]
  rw [Finset.sum_range_succ']
  have hs : (∑ t ∈ Finset.range (stopTime (shift ω) (next ω i)),
      if level ω i (t+1) ≠ 0 ∧ ω (t+1) = true then 1 else 0) =
      (∑ t ∈ Finset.range (stopTime (shift ω) (next ω i)),
      if level (shift ω) (next ω i) t ≠ 0 ∧ (shift ω) t = true then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [level_shift ω i t hi]
    rfl
  rw [hs]
  simp [level, hi.ne', Nat.add_comm]


theorem solution (ω : Tape) (i : ℕ) (hi : 0 < i) (h : ∃ t, level (fun n => ω (n+1)) (if ω 0 then i+2 else i-1) t = 0) : upwardCount ω i = (if ω 0 then 1 else 0) + upwardCount (fun n => ω (n+1)) (if ω 0 then i+2 else i-1) := by
  exact first_step_count ω i hi h
