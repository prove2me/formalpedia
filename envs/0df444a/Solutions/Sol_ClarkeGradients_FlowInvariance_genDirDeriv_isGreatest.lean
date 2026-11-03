-- Prove2me | solution 1 for ClarkeGradients.FlowInvariance.genDirDeriv_isGreatest
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T19:23:47.3602+00:00
-- url     : https://prove2.me/submissions/7a3055e9-6244-457b-937b-3d48d6a0ac9e

import Theorems.Thm_ClarkeGradients_MaxFunctions_genDirDeriv_isGreatest

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
open ClarkeGradients


/-- Clarke (1975), Proposition (1.4): for locally Lipschitz `f`,
`f°(x; v) = max {ζ · v : ζ ∈ ∂f(x)}`, i.e. `f°(x; ·)` is the support function of `∂f(x)`. -/
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Shared.LipschitzOnBounded f) (x v : EuclideanSpace ℝ (Fin n)) :
    IsGreatest ((fun ζ => inner ℝ ζ v) '' Shared.generalizedGradient f x) (Shared.genDirDeriv f x v) :=
  ClarkeGradients.MaxFunctions.genDirDeriv_isGreatest f hf x v