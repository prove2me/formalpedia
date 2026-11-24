-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.sum_C_one_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:40:07.354471+00:00
-- url     : https://prove2.me/submissions/7fdba135-614c-457a-ad9f-e083b724d266

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX

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
variable {R B : Type*} [CommRing R] [CommRing B] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
  (φ : R →+* B) (a b : Fin n) (t : B)
namespace Formalism.MainNotions.G.GLWeightTheory
theorem _root_.solution (l : ι) (c : Fin n) :
    ∑ b' : Fin n, C ((1 : Matrix (Fin n) (Fin n) B) c b') * (X (l, b') : MvPolynomial (ι × Fin n) B) = X (l, c) := by
  rw [Finset.sum_eq_single c]
  · simp
  · intro b' _ hb
    simp [Matrix.one_apply_ne (Ne.symm hb)]
  · simp
end Formalism.MainNotions.G.GLWeightTheory
