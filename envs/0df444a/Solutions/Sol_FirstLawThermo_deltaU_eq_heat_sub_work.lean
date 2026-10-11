-- Prove2me | solution 1 for FirstLawThermo.deltaU_eq_heat_sub_work
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T13:15:23.305807+00:00
-- url     : https://prove2.me/submissions/6ce976ba-ecd1-423a-aaa4-a16af5e716f5

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem solution {σ : Type*} (U : σ → ℝ) (p : Process σ) :
    U p.finish - U p.start = heat U p - p.work := by
  unfold heat
  ring
