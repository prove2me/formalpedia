-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.perpS_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:27:08.499308+00:00
-- url     : https://prove2.me/submissions/04c94e8b-b47e-4f1d-beb2-78b713e07faa

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_mem_perpS
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_E
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_fischerAdjointness_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r)
    {A : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])} (hA : (GAe p LL j e).Stable A) :
    (GAe p LL j e).Stable (perpS A) := by
  intro a b y hy
  rw [mem_perpS] at hy ⊢
  intro x hx
  have hmem := hA b a x hx
  rw [GAe_E] at hmem ⊢
  rw [← fischerAdjointness_holds p N r LL j (e b) (e a) x y]
  exact hy _ hmem
end Formalism.InvariantFactorPaths.PW
