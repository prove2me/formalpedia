-- Prove2me | solution 1 for Formalism.MainNotions.G.GLWeightTheory.sum_C_single_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:40:09.18027+00:00
-- url     : https://prove2.me/submissions/f46b652c-6aab-435b-9243-3dee8f1d5bd6

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
theorem _root_.solution (s : B) (l : ι) (c : Fin n) :
    ∑ b' : Fin n, C (Matrix.single a b s c b') * (X (l, b') : MvPolynomial (ι × Fin n) B) =
      if c = a then C s * X (l, b) else 0 := by
  by_cases hc : c = a
  · subst hc
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb
      simp [Ne.symm hb]
    · simp
  · simp [hc, Ne.symm hc]
end Formalism.MainNotions.G.GLWeightTheory
