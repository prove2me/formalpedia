-- Prove2me | solution 1 for Formalism.REAL.exp_conjTranspose_of_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:42:50.104918+00:00
-- url     : https://prove2.me/submissions/1e54dbba-8455-42ee-8124-ee78bb973c85

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
theorem _root_.solution {A : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ = A) :
    (NormedSpace.exp A)ᴴ = NormedSpace.exp A := by
  rw [← Matrix.exp_conjTranspose, hA]
end Formalism.REAL
