-- Prove2me | solution 1 for Formalism.REAL.exp_add_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:10.550798+00:00
-- url     : https://prove2.me/submissions/86eda330-543f-4d0d-8ee9-19f5bffd55c3

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
theorem _root_.solution (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (A + A) = NormedSpace.exp A * NormedSpace.exp A := Matrix.exp_add_of_commute _ _ (Commute.refl A)
end Formalism.REAL
