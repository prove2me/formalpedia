-- Prove2me | solution 1 for FamousTheorems.fredholm_alternative
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:59:56.512667+00:00
-- url     : https://prove2.me/submissions/fe897036-da31-4057-889d-73602039bf3b

import Mathlib

theorem solution {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    {T : X →L[𝕜] X} (hT : IsCompactOperator T) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (T : X →ₗ[𝕜] X) μ ∨ μ ∈ resolventSet 𝕜 T :=
  hT.hasEigenvalue_or_mem_resolventSet hμ
