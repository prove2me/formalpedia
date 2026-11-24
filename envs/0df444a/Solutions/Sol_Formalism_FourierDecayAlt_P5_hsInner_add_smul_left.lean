-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.hsInner_add_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:51:06.573797+00:00
-- url     : https://prove2.me/submissions/8c7ea7c4-5abb-4652-bc5a-0df4c7a0e59d

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (A A' C : Wq →L[ℂ] Wp) (a : ℂ) :
    B.hsInner (A + a • A') C = B.hsInner A C + a * B.hsInner A' C := by
  simp only [B.hsInner, B.hsVec, PiLp.inner_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, inner_add_right, inner_smul_right, Finset.sum_add_distrib, Finset.mul_sum]
end Formalism.FourierDecayAlt.P5
