-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.Hpk_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:11:53.807589+00:00
-- url     : https://prove2.me/submissions/8e15bd78-7655-4737-915b-cc892772f859

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h : (Hpk k r).det * (Hpk k r).det = 1 := by rw [← Matrix.det_mul, Hpk_sq, Matrix.det_one]
  exact isUnit_iff_ne_zero.mpr (fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h)
end Formalism.FourierDecayAlt.P.B2x8
