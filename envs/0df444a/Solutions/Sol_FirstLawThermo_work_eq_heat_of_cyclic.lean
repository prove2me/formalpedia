-- Prove2me | solution 1 for FirstLawThermo.work_eq_heat_of_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T13:15:25.245099+00:00
-- url     : https://prove2.me/submissions/1360cbea-0a4f-43a8-b711-cfee1c36ae60

import Definitions.Def_FirstLawThermo_Defs
import Mathlib

open FirstLawThermo

theorem solution {σ : Type*} (U : σ → ℝ) (p : Process σ)
    (hcyc : p.IsCyclic) :
    p.work = heat U p := by
  unfold heat
  unfold Process.IsCyclic at hcyc
  rw [hcyc, sub_self, zero_add]
