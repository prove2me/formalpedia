-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.extend_by_zero_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:48:02.048181+00:00
-- url     : https://prove2.me/submissions/84d9c3dd-91ce-4c21-be64-f934eb078aff

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TorusArgumentMultiplicative

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate InnerProductSpace ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.ExtendZeroPSD := by
  intro ι _ _ S _ K hK
  classical
  let P : Matrix S ι ℂ := Matrix.of fun s w => if (s : ι) = w then 1 else 0
  convert hK.conjTranspose_mul_mul_same P using 1
  ext w w'
  simp only [P, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases hw : w ∈ S <;> by_cases hw' : w' ∈ S
  · rw [dif_pos ⟨hw, hw'⟩]
    rw [Finset.sum_eq_single ⟨w', hw'⟩]
    · rw [Finset.sum_eq_single ⟨w, hw⟩]
      · simp
      · intro s _ hs; have : (s : ι) ≠ w := fun h => hs (Subtype.ext h); simp [this]
      · simp
    · intro s _ hs; have : (s : ι) ≠ w' := fun h => hs (Subtype.ext h); simp [this]
    · simp
  all_goals
    rw [dif_neg (by tauto)]
    symm
    apply Finset.sum_eq_zero
    intro s _
  · have : (s : ι) ≠ w' := fun h => hw' (h ▸ s.2); simp [this]
  · have : ∀ t : S, (t : ι) ≠ w := fun t h => hw (h ▸ t.2); simp [this]
  · have : ∀ t : S, (t : ι) ≠ w := fun t h => hw (h ▸ t.2); simp [this]
end Formalism.FourierDecayAlt.P
