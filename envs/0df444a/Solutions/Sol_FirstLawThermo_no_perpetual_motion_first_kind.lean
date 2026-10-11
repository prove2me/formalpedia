-- Prove2me | solution 1 for FirstLawThermo.no_perpetual_motion_first_kind
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T13:15:25.656174+00:00
-- url     : https://prove2.me/submissions/7ef23049-79df-4cfe-a2e4-5a49042e4cb9

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem solution {σ : Type*} (procs : Set (Process σ))
    (U : σ → ℝ) (hU : IsInternalEnergy procs U) (p : Process σ) (hp : p ∈ procs)
    (had : p.adiabatic) (hcyc : p.IsCyclic) :
    p.work = 0 := by
  have h := hU p hp had
  unfold Process.IsCyclic at hcyc
  rw [hcyc, sub_self] at h
  linarith
