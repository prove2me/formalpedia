-- Prove2me | solution 1 for BB5.champion_halts
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-22T14:43:51.940713+00:00
-- url     : https://prove2.me/submissions/bf298d53-bb22-487d-a32e-d33f152923a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_winner
import Definitions.Def_BB5_gcfg
import Theorems.Thm_BB5_g_3x
import Theorems.Thm_BB5_g_3x1
import Theorems.Thm_BB5_g_3x2

open FCP.BusyBeaver

/-- Iterating `run` splits over addition of step counts. -/
private lemma run_add (M : TM 5) (c : Config 5) (a b : ℕ) :
    run M c (a + b) = (run M c a).bind (fun c' => run M c' b) := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
      rw [Nat.add_succ, run, ih]
      simp [run, Option.bind_assoc]

/-- If the machine is still running after `a` steps, it was not halted at any
earlier step. -/
private lemma run_ne_none_before {c c' : Config 5} {a : ℕ}
    (ha : run BB5.winner c a = some c') {s : ℕ} (hs : s ≤ a) :
    run BB5.winner c s ≠ none := by
  intro hsnone
  have h := run_add BB5.winner c s (a - s)
  have hsa : s + (a - s) = a := Nat.add_sub_of_le hs
  rw [hsa, ha, hsnone] at h
  simp at h

/-- Concatenating a non-halting run and a second run. -/
private lemma chain_run {c c' c'' : Config 5} {a b : ℕ}
    (ha : run BB5.winner c a = some c') (hb : run BB5.winner c' b = some c'') :
    run BB5.winner c (a + b) = some c'' := by
  rw [run_add, ha]
  simpa using hb

/-- Concatenating a non-halting run and a halting run. -/
private lemma chain_halts {c c' : Config 5} {a b : ℕ}
    (ha : run BB5.winner c a = some c') (hb : HaltsIn BB5.winner c' b) :
    HaltsIn BB5.winner c (a + b) := by
  constructor
  · rw [run_add, ha]
    exact hb.1
  · intro s hs
    by_cases hsa : s ≤ a
    · exact run_ne_none_before ha hsa
    · have hsu : s = a + (s - a) := by omega
      have hub : s - a < b := by omega
      rw [hsu, run_add, ha]
      simpa using hb.2 (s - a) hub

/-- The champion's blank-tape trajectory, read off from the three Collatz-like
rules:
    0 → 6 → 16 → 34 → 64 → 114 → 196 → 334 → 564 → 946
      → 1584 → 2646 → 4416 → 7366 → 12284 → halt.
The step counts sum to 47,176,870. -/
theorem solution :
    FCP.BusyBeaver.HaltsIn BB5.winner (FCP.BusyBeaver.init (by omega)) 47176870 := by
  have h0 : run BB5.winner (BB5.gcfg 0) 15 = some (BB5.gcfg 6) := by
    simpa using (BB5.g_3x 0)
  have h1 := chain_run h0 (by simpa using (BB5.g_3x 2))
  norm_num at h1
  have h2 := chain_run h1 (by simpa using (BB5.g_3x1 5))
  norm_num at h2
  have h3 := chain_run h2 (by simpa using (BB5.g_3x1 11))
  norm_num at h3
  have h4 := chain_run h3 (by simpa using (BB5.g_3x1 21))
  norm_num at h4
  have h5 := chain_run h4 (by simpa using (BB5.g_3x 38))
  norm_num at h5
  have h6 := chain_run h5 (by simpa using (BB5.g_3x1 65))
  norm_num at h6
  have h7 := chain_run h6 (by simpa using (BB5.g_3x1 111))
  norm_num at h7
  have h8 := chain_run h7 (by simpa using (BB5.g_3x 188))
  norm_num at h8
  have h9 := chain_run h8 (by simpa using (BB5.g_3x1 315))
  norm_num at h9
  have h10 := chain_run h9 (by simpa using (BB5.g_3x 528))
  norm_num at h10
  have h11 := chain_run h10 (by simpa using (BB5.g_3x 882))
  norm_num at h11
  have h12 := chain_run h11 (by simpa using (BB5.g_3x 1472))
  norm_num at h12
  have h13 := chain_run h12 (by simpa using (BB5.g_3x1 2455))
  norm_num at h13
  have hf : HaltsIn BB5.winner (BB5.gcfg 12284) 24576 := by
    simpa using (BB5.g_3x2 4094)
  have hfinal := chain_halts h13 hf
  norm_num at hfinal
  simpa [BB5.gcfg_zero_eq_init] using hfinal
