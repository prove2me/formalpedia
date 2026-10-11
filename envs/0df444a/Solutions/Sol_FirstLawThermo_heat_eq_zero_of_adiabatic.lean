-- Prove2me | solution 1 for FirstLawThermo.heat_eq_zero_of_adiabatic
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T13:15:23.879012+00:00
-- url     : https://prove2.me/submissions/6a3333be-2b71-4c13-b38b-fe2452a3a7b3

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem solution {σ : Type*} (procs : Set (Process σ))
    (U : σ → ℝ) (hU : IsInternalEnergy procs U) (p : Process σ) (hp : p ∈ procs)
    (had : p.adiabatic) :
    heat U p = 0 := by
  have h := hU p hp had
  unfold heat
  linarith
