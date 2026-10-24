-- Prove2me | solution 1 for AvramDividend.Classical.nat_capped_first_hit_eventually_stabilizes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:12:20.619384+00:00
-- url     : https://prove2.me/submissions/2df816a4-d599-4458-877b-acc0282b3c03

import Mathlib.Probability.Process.HittingTime
import Mathlib.Data.Nat.Find
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (u : ℕ → ℝ) (s : Set ℝ) (h : ∃ j : ℕ, u j ∈ s) :
    ∃ j : ℕ, u j ∈ s ∧
      ∀ m : ℕ, j ≤ m →
        hittingBtwn (fun k (_ : Unit) => u k) s 0 m () = j := by
  classical
  let j : ℕ := Nat.find h
  have hj : u j ∈ s := Nat.find_spec h
  let v : ℕ → Unit → ℝ := fun k _ => u k
  have hex : ∃ k ∈ Set.Icc 0 j, v k () ∈ s := by
    exact ⟨j, by simp, hj⟩
  have hmem : u (hittingBtwn v s 0 j ()) ∈ s := by
    exact hittingBtwn_mem_set (u := v) (s := s) (n := 0)
      (m := j) (ω := ()) hex
  have hmin : j ≤ hittingBtwn v s 0 j () :=
    Nat.find_le (h := h) hmem
  have hmax : hittingBtwn v s 0 j () ≤ j :=
    hittingBtwn_le (u := v) (s := s) (n := 0) (m := j) ()
  have heq : hittingBtwn v s 0 j () = j :=
    le_antisymm hmax hmin
  refine ⟨j, hj, ?_⟩
  intro m hm
  have hsame : hittingBtwn v s 0 j () = hittingBtwn v s 0 m () :=
    hittingBtwn_eq_hittingBtwn_of_exists
      (u := v) (s := s) (n := 0) (ω := ()) hm hex
  exact hsame.symm.trans heq
