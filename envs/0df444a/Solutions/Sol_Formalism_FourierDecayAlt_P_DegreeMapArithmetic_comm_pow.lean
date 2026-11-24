-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DegreeMapArithmetic.comm_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:54:05.804325+00:00
-- url     : https://prove2.me/submissions/afc5ce60-5451-41c3-9bdb-7dd458c7e8f2

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DegreeMapArithmetic
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.DegreeMapArithmetic
theorem _root_.solution (H f : Module.End ℂ V) (d : ℂ) (h : H * f = f * H + d • f) (k : ℕ) :
    H * f ^ k = f ^ k * H + ((k : ℂ) * d) • f ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, ih, add_mul, mul_assoc, h]
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, mul_assoc, Nat.cast_succ, add_smul, one_mul]
    abel
end Formalism.FourierDecayAlt.P.DegreeMapArithmetic
