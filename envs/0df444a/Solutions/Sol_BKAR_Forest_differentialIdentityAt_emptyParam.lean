-- Prove2me | solution 1 for BKAR.Forest.differentialIdentityAt_emptyParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:44.634327+00:00
-- url     : https://prove2.me/submissions/99c2e56e-8b0c-409e-9b92-cb6f961aa298

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_differentialIdentityAt_empty

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ (constantConfig t)) :
    deriv (fun s : ℝ => ρ (constantConfig s)) t =
      Finset.sum (Finset.univ : Finset (Edge V))
        (fun e => partialDeriv e ρ (constantConfig t)) :=
  differentialIdentityAt_empty emptyParam hρ
end BKAR.Forest
