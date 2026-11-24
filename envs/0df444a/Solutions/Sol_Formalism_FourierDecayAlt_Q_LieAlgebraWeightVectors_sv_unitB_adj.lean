-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_unitB_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:50:47.494805+00:00
-- url     : https://prove2.me/submissions/ad82ae39-fb4c-4e3f-9983-bda2f0c6d590

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (a b : Fin m)
    (v : Fin (2 * r + k + 1) → ℂ) :
    (unitB (Hpk k r) Bs a b)ᴴ *ᵥ (Hpk k r *ᵥ v) =
      herm (Hpk k r) v (Bs a) • fun p => star (herm (Hpk k r) (bvec p) (Bs b)) := by
  ext p
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, unitB, Matrix.of_apply, star_mul',
    Pi.smul_apply, smul_eq_mul]
  unfold herm
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply]
  ring
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
