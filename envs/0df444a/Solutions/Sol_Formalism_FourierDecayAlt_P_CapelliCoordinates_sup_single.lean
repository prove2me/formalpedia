-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliCoordinates.sup_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:35:58.513066+00:00
-- url     : https://prove2.me/submissions/8a240cf2-30b7-42e3-8b45-5c067db6e7ba

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace CapelliCoordinates
section Parts
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Parts
section Sup
variable {k r : ℕ} {i : Fin (r + 1)}
private theorem sup_single_of_inV (p q : Fin (2 * r + k + 1)) (hp : Qx2.inV k r i p) (hq : Qx2.inV k r i q) :
    Sup k r i (Matrix.single p q (1 : ℂ)) := by
  have hi := i.isLt
  have hcol : ∀ (M : Mx k r) (x y : Fin (2 * r + k + 1)), (M *ᵥ bvec x) y = M y x := by
    intro M x y
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hz : ∀ x y : Fin (2 * r + k + 1), Qx2.inV k r i x → ¬ Qx2.inV k r i y → Hpk k r x y = 0 := by
    intro x y hx hy
    have hne : x ≠ y := by rintro rfl; exact hy hx
    simp only [Qx2.inV] at hx hy
    simp only [Hpk, hne, and_false, ↓reduceIte]
    rw [if_neg (by omega), if_neg (by omega)]
  intro x hx
  have hne : q ≠ x := by rintro rfl; exact hx hq
  refine ⟨?_, ?_⟩
  · ext y
    rw [hcol]
    simp [Matrix.single_apply, hne]
  · ext y
    rw [hcol, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz' : z = p
    · subst hz'
      rw [hz _ _ hp hx, mul_zero]
    · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro w _
      simp [Matrix.conjTranspose_apply, Matrix.single_apply, Ne.symm hz']
end Sup
section Lin
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
end Lin
end CapelliCoordinates
namespace CapelliCoordinates
section Cap
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
end Cap
end CapelliCoordinates
namespace CapelliCoordinates
section Frame
variable {k r : ℕ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Mx k r)}
end Frame
end CapelliCoordinates
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.CapelliCoordinates
variable {k r : ℕ} {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.CapelliCoordinates
theorem _root_.solution (a b : Fin (mdim k r i)) : Sup k r i (Matrix.single (posL k r i a) (posL k r i b) 1) := by
  have hj := a.isLt
  have hj' := b.isLt
  have hi := i.isLt
  apply sup_single_of_inV <;> simp only [Qx2.inV, posL, mdim] at hj hj' ⊢ <;> omega
end Formalism.FourierDecayAlt.P.CapelliCoordinates
