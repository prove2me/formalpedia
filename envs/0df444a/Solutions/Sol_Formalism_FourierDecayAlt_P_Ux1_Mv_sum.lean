-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.Mv_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:53.204427+00:00
-- url     : https://prove2.me/submissions/ed5326f4-8e0d-4c61-9eb4-d1db58acaa0f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution (Y : J k r → ℝ) : Mv Y = ∑ i, Y i • Eb i := by
  ext p q
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Eb, Matrix.of_apply, Mv, smul_ite, smul_zero, ite_and]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Complex.real_smul, mul_one, if_true, if_false, Bool.false_eq_true]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q, Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp [add_comm]
  all_goals first | (intro b _ hb; simp [Ne.symm hb]) | simp
end Formalism.FourierDecayAlt.P.Ux1
