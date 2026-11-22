-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.matrixSubst_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:27.472811+00:00
-- url     : https://prove2.me/submissions/3acf4220-21bf-4591-b216-2e6965f58f2e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_comp
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_one

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
theorem _root_.solution (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (F : MvPolynomial (ι × Fin n) R) :
    matrixSubst LL S (RingHom.id B) m m' (MvPolynomial.map φ F) = matrixSubst LL S φ m m' F := by
  rw [← matrixSubst_one LL S, matrixSubst_comp, mul_one, one_mul]
end Formalism.MainNotions.G.GLWeightTheory
