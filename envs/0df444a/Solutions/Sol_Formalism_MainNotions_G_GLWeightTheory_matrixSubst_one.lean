-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.matrixSubst_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:29:41.453829+00:00
-- url     : https://prove2.me/submissions/0d963d72-67d9-421e-b43b-2035fd69485c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_C
import Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_X

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
theorem _root_.solution (φ : R →+* B) (F : MvPolynomial (ι × Fin n) R) :
    matrixSubst LL S φ 1 1 F = MvPolynomial.map φ F := by
  classical
  have : matrixSubst LL S φ (1 : Matrix (Fin n) (Fin n) B) 1 = MvPolynomial.map φ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [matrixSubst_C]
    · intro v
      simp only [matrixSubst_X, map_X]
      split_ifs <;> simp [Matrix.one_apply]
  exact congrArg (fun f => f F) this
end Formalism.MainNotions.G.GLWeightTheory
