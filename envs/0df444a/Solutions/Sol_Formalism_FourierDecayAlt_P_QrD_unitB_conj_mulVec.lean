-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QrD.unitB_conj_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:51:35.124961+00:00
-- url     : https://prove2.me/submissions/e83ac614-94aa-4ae4-a6ea-27b2712b70bd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneParameterDifferentiable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.QrD
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.QrD
theorem _root_.solution {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (Bs : Fin m → Fin n → ℂ) (a b : Fin m)
    (v : Fin n → ℂ) (h : herm H v (Bs a) = 0) : (unitB H Bs a b)ᴴ *ᵥ (H *ᵥ v) = 0 := by
  ext q
  have h' : ∑ p, star (Bs a p) * (H *ᵥ v) p = 0 := h
  show ∑ p, star (Bs a p * (star (Bs b) ⬝ᵥ H *ᵥ bvec q)) * (H *ᵥ v) p = 0
  simp_rw [star_mul']
  rw [show ∑ p, star (Bs a p) * star (star (Bs b) ⬝ᵥ H *ᵥ bvec q) * (H *ᵥ v) p
      = star (star (Bs b) ⬝ᵥ H *ᵥ bvec q) * ∑ p, star (Bs a p) * (H *ᵥ v) p from by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring, h', mul_zero]
end Formalism.FourierDecayAlt.P.QrD
