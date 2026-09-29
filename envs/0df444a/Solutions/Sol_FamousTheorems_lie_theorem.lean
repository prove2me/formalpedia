-- Prove2me | solution 1 for FamousTheorems.lie_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:16:58.393998+00:00
-- url     : https://prove2.me/submissions/2f717f70-8884-44e2-a4b8-acad409e9d4b

import Mathlib

theorem solution (k : Type*) [Field k] (L : Type*) [LieRing L] [LieAlgebra k L] (V : Type*) [AddCommGroup V]
    [Module k V] [LieRingModule L V] [LieModule k L V] [CharZero k] [Module.Finite k V] [Nontrivial V]
    [LieAlgebra.IsSolvable L] [LieModule.IsTriangularizable k L V] :
    ∃ χ : Module.Dual k L, Nontrivial (LieModule.weightSpace V ⇑χ) :=
  LieModule.exists_nontrivial_weightSpace_of_isSolvable k L V
