-- Prove2me | solution 1 for FamousTheorems.jordan_chevalley_dunford
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:27:45.192455+00:00
-- url     : https://prove2.me/submissions/24b6ff33-f262-41ce-a309-e3ab4a6300fa

import Mathlib

theorem solution {K V : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) :
    ∃ n ∈ Algebra.adjoin K {f}, ∃ s ∈ Algebra.adjoin K {f}, IsNilpotent n ∧ s.IsSemisimple ∧ f = n + s :=
  Module.End.exists_isNilpotent_isSemisimple
