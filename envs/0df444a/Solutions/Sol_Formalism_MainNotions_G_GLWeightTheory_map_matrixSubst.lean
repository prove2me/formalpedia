-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.map_matrixSubst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:14.839361+00:00
-- url     : https://prove2.me/submissions/12e98390-3d23-4969-b47d-3c8dc8e043fa

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
theorem _root_.solution (φ : R →+* B) (ψ : B →+* B') (m m' : Matrix (Fin n) (Fin n) B)
    (F : MvPolynomial (ι × Fin n) R) :
    MvPolynomial.map ψ (matrixSubst LL S φ m m' F) = matrixSubst LL S (ψ.comp φ) (m.map ψ) (m'.map ψ) F := by
  classical
  have : (MvPolynomial.map ψ).comp (matrixSubst LL S φ m m') = matrixSubst LL S (ψ.comp φ) (m.map ψ) (m'.map ψ) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [matrixSubst_C]
    · intro v
      simp only [RingHom.comp_apply, matrixSubst_X]
      split_ifs <;> simp
  exact congrArg (fun f => f F) this
end Formalism.MainNotions.G.GLWeightTheory
