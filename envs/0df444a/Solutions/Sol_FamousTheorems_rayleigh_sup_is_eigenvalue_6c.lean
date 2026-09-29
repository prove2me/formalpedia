-- Prove2me | solution 1 for FamousTheorems.rayleigh_sup_is_eigenvalue_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:49:53.915632+00:00
-- url     : https://prove2.me/submissions/e69c7fd9-4491-469f-8077-31ce4f7620c3

import Mathlib

theorem solution {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [Nontrivial E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) :
    Module.End.HasEigenvalue T
      ((⨆ x : { x : E // x ≠ 0 }, RCLike.re (inner 𝕜 (T x) (x : E)) / ‖(x : E)‖ ^ 2 : ℝ) : 𝕜) :=
  hT.hasEigenvalue_iSup_of_finiteDimensional
