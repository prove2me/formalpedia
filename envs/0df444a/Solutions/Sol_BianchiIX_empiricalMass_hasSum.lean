-- Prove2me | solution 1 for BianchiIX.empiricalMass_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:11:20.717654+00:00
-- url     : https://prove2.me/submissions/2406b40f-a4cc-42c5-94e9-9df011ad89ed

import Definitions.Def_BianchiIX_Statistics_EmpiricalMass
import Theorems.Thm_BianchiIX_empiricalMass_weighted_hasSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Filter
open scoped Topology
open BianchiIX
noncomputable section
open scoped Classical


theorem solution {ι : Type*} (label : ℕ → ι) (N : ℕ) :
    HasSum (empiricalMass label N) 1 := by
  simpa [show (N : ℝ) + 1 ≠ 0 by positivity] using
    empiricalMass_weighted_hasSum label N (fun _ => 1)
