-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x9.nu_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:20:41.093366+00:00
-- url     : https://prove2.me/submissions/c0fc933e-178e-4a1d-86e3-347ab1f36fb8

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_Psi_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_mC_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_prod_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_vol_ne

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x9
theorem _root_.solution (μG₁ : Measure (Mt k r')) [SFinite μG₁] (h0 : μG₁ ≠ 0) : nu μG₁ ≠ 0 := by
  unfold nu
  rw [Ne, Measure.map_eq_zero_iff Psi_meas.aemeasurable]
  exact prod_ne _ _ mC_ne (prod_ne _ _ vol_ne h0)
end Formalism.FourierDecayAlt.P.B2x9
