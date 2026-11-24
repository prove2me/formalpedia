-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.dj_aDil_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:07:14.10015+00:00
-- url     : https://prove2.me/submissions/bc37238a-da26-41f4-8d00-e7be97b35e89

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : IsUnit (aDil k r t).det := by
  unfold aDil
  rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  split_ifs
  · exact_mod_cast pow_ne_zero _ ht
  · exact one_ne_zero
  · exact_mod_cast inv_ne_zero (pow_ne_zero _ ht)
end Formalism.FourierDecayAlt.P.B2x8
