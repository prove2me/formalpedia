-- Prove2me | solution 1 for FirstLawThermo.isInternalEnergy_add_const
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T13:15:21.875419+00:00
-- url     : https://prove2.me/submissions/672ce37b-75e8-4f97-818f-29f281095fba

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem solution {σ : Type*} (procs : Set (Process σ))
    (U : σ → ℝ) (hU : IsInternalEnergy procs U) (c : ℝ) :
    IsInternalEnergy procs (fun A => U A + c) := by
  intro p hp had
  have h := hU p hp had
  simp only
  linarith
