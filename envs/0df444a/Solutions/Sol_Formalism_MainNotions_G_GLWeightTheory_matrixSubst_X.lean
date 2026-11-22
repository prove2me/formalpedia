-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.matrixSubst_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:39.423157+00:00
-- url     : https://prove2.me/submissions/330f3285-8611-4dfb-b151-7463dea09d62

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
open Classical
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (v : ι × Fin n) :
    matrixSubst LL S φ m m' (X v) = if v.1 ∈ S then
      (if LL.vec v.1 then ∑ b : Fin n, MvPolynomial.C (m b v.2) * X (v.1, b)
       else ∑ b : Fin n, MvPolynomial.C (m' v.2 b) * X (v.1, b))
    else X v := by
  simp [matrixSubst]
end Formalism.MainNotions.G.GLWeightTheory
