-- Prove2me | solution 1 for Formalism.REAL.polar_log_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:46:20.530801+00:00
-- url     : https://prove2.me/submissions/73e0f209-a288-42b7-abf9-52fd859f9f89

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (g : Matrix (Fin n) (Fin n) ℂ) : (polarLog g)ᴴ = polarLog g := by
  have h1 : IsSelfAdjoint (CFC.log (gᴴ * g)) := by
    first
    | exact cfc_predicate Real.log (gᴴ * g)
    | exact CFC.log_isSelfAdjoint
  have h2 : IsSelfAdjoint ((1 / 2 : ℝ) • CFC.log (gᴴ * g)) := IsSelfAdjoint.smul (IsSelfAdjoint.all _) h1
  exact h2
end Formalism.REAL
