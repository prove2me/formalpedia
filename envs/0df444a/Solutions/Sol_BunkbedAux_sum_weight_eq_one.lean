-- Prove2me | solution 1 for BunkbedAux.sum_weight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-11T18:39:25.425259+00:00
-- url     : https://prove2.me/submissions/66fb04c2-4948-4d96-ae62-524f106626b6

import Definitions.Def_BunkbedPercolation

open Bunkbed Finset

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) : ∑ S ∈ E.powerset, weight E w S = 1 := by
  have h := Finset.prod_add w (fun e => 1 - w e) E
  simp only [add_sub_cancel, Finset.prod_const_one] at h
  simpa [weight] using h.symm
