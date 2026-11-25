-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliCoordinates.herm_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:51.662953+00:00
-- url     : https://prove2.me/submissions/ff5a59c2-0dd0-45f8-88d9-464f55a1f3c9

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
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
end Sup
section Lin
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
end Lin
end CapelliCoordinates
namespace CapelliCoordinates
section Cap
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
private theorem herm_bvec_eq_zero_of_not_inV {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) {p : Fin (2 * r + k + 1)}
    (hp : ¬ Qx2.inV k r (Fin.last r) p) : herm (Hpk k r) (bvec p) v = 0 := by
  have hcol : ∀ q, (Hpk k r *ᵥ bvec p) q = Hpk k r q p := by
    intro q
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  unfold Qx2.inV at hp
  simp only [Fin.val_last] at hp
  unfold herm
  simp only [dotProduct, hcol]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hq : q.val < r ∨ r + k < q.val
  · simp [hv q hq]
  · have hp' : p.val < r ∨ r + k < p.val := by omega
    have hne : q ≠ p := fun h => by subst h; omega
    have h0 : Hpk k r q p = 0 := by
      simp only [Hpk, hne, and_false, ↓reduceIte]
      rw [if_neg (by omega), if_neg (by omega)]
    rw [h0, mul_zero]
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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.CapelliCoordinates
theorem _root_.solution {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) {p : Fin (2 * r + k + 1)}
    (hp : ¬ Qx2.inV k r (Fin.last r) p) : herm (Hpk k r) (bvec p) v = 0 := herm_bvec_eq_zero_of_not_inV hv hp
end Formalism.FourierDecayAlt.P.CapelliCoordinates
