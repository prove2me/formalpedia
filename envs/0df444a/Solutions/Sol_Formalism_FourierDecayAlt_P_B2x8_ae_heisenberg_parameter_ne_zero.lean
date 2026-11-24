-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.ae_heisenberg_parameter_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:03:34.239872+00:00
-- url     : https://prove2.me/submissions/a4be5167-b488-4bc0-8569-64b57caadaf5

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_ae_second_coordinate_ne_zero

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
theorem _root_.solution : ∀ᵐ p : ℂ × HPar k r' ∂(μx.prod (volume : Measure (HPar k r'))), p.2.2 ≠ 0 := by
  rw [ae_iff]
  have h0 := ae_second_coordinate_ne_zero (k := k) (r' := r')
  rw [ae_iff] at h0
  have : {p : ℂ × HPar k r' | ¬ p.2.2 ≠ 0} = Set.univ ×ˢ {q : HPar k r' | ¬ q.2 ≠ 0} := by ext p; simp
  rw [this, Measure.prod_prod, h0, mul_zero]
end Formalism.FourierDecayAlt.P.B2x8
