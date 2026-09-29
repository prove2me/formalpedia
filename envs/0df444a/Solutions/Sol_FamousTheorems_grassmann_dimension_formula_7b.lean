-- Prove2me | solution 1 for FamousTheorems.grassmann_dimension_formula_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:53:02.793507+00:00
-- url     : https://prove2.me/submissions/5517cd09-37a5-4920-adfc-18d8d4814c47

import Mathlib

theorem solution {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] (U W : Submodule K V)
    [FiniteDimensional K U] [FiniteDimensional K W] :
    Module.finrank K ↥(U ⊔ W) + Module.finrank K ↥(U ⊓ W) = Module.finrank K U + Module.finrank K W :=
  Submodule.finrank_sup_add_finrank_inf_eq U W
