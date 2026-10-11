-- Prove2me | solution 1 for FirstLawThermo.heat_eq_deltaU_of_adynamic
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T13:15:24.313723+00:00
-- url     : https://prove2.me/submissions/994cd231-8397-49e8-8e27-8196f8be61cf

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem solution {σ : Type*} (U : σ → ℝ) (p : Process σ)
    (hp : p.IsAdynamic) :
    heat U p = U p.finish - U p.start := by
  unfold heat
  unfold Process.IsAdynamic at hp
  rw [hp, add_zero]
