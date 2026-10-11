-- Prove2me | solution 1 for FirstLawThermo.heat_add_const
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T13:15:24.778399+00:00
-- url     : https://prove2.me/submissions/6312b206-1f67-424b-8109-4fa814872528

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem solution {σ : Type*} (U : σ → ℝ) (c : ℝ) (p : Process σ) :
    heat (fun A => U A + c) p = heat U p := by
  unfold heat
  ring
