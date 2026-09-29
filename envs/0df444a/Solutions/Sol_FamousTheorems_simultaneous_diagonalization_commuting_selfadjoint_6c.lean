-- Prove2me | solution 1 for FamousTheorems.simultaneous_diagonalization_commuting_selfadjoint_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:50:09.532118+00:00
-- url     : https://prove2.me/submissions/e4a30eb1-c381-46aa-9aaa-c18af30817d9

import Mathlib

theorem solution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    DirectSum.IsInternal fun i : 𝕜 × 𝕜 => Module.End.eigenspace A i.2 ⊓ Module.End.eigenspace B i.1 :=
  hA.directSum_isInternal_of_commute hB hAB
