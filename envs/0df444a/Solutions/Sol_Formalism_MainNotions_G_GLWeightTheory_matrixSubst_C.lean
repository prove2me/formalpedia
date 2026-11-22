-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.matrixSubst_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:35.991655+00:00
-- url     : https://prove2.me/submissions/3ea93618-ffd2-40b1-8c7d-23a541422959

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
variable {R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (c : R) :
    matrixSubst LL S φ m m' (C c) = C (φ c) := by
  simp [matrixSubst]
end Formalism.MainNotions.G.GLWeightTheory
