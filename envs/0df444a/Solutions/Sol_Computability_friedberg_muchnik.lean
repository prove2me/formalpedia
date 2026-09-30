-- Prove2me | solution 1 for Computability.friedberg_muchnik
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T20:04:54.69943+00:00
-- url     : https://prove2.me/submissions/bc70d5ac-4c92-4145-b9bb-ae32091ae48f

import Theorems.Thm_FriedbergMuchnik_oracle_programs_exact
import Theorems.Thm_FriedbergMuchnik_recursive_projection_re
import Theorems.Thm_FriedbergMuchnik_stage_membership_computable
import Theorems.Thm_FriedbergMuchnik_priority_requirements_met

open Computability FriedbergMuchnik

theorem solution :
    ∃ A B : Set ℕ,
      CEnumerable A ∧ CEnumerable B ∧ TuringIncomparable A B := by
  classical
  have hce (i : Bool) : CEnumerable (limitSet i) := by
    have hcomp : Computable (fun p : ℕ × ℕ => decide (p.1 ∈ stageList i p.2)) :=
      stage_membership_computable.decide.comp
        (Computable.snd.pair ((Computable.const i).pair Computable.fst))
    exact recursive_projection_re (fun n s => n ∈ stageList i s) hcomp.computablePred
  have hnot (i : Bool) : ¬ SetTuringReducible (limitSet (!i)) (limitSet i) := by
    intro h
    obtain ⟨c, hc⟩ := (oracle_programs_exact _ _).mp h
    obtain ⟨x, hcase⟩ := priority_requirements_met i c
    rcases hcase with ⟨hx, hzero⟩ | ⟨hx, hzero⟩
    · rw [hc] at hzero
      simp [setOracle, PFun.lift, hx] at hzero
    · apply hzero
      rw [hc]
      simp [setOracle, PFun.lift, hx]
  exact ⟨limitSet false, limitSet true, hce false, hce true, hnot true, hnot false⟩
