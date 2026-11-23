-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.muBlock_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:22.452375+00:00
-- url     : https://prove2.me/submissions/1e479f20-6507-47fd-80b1-11912b8518f3

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_muPi_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution (β : ℂ) (n : ℕ) : ∃ k : NNReal, muBlock β n = k • (volume : Measure (BlockCoord n)) := by
  refine ⟨(Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card (Fin n) *
    ((Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card (UT n) *
      (Real.toNNReal (‖β‖ / (2 * Real.pi))) ^ Fintype.card (Fin n)), ?_⟩
  unfold muBlock
  rw [muPi_eq, muPi_eq]
  simp only [ENNReal.smul_def, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ENNReal.coe_mul, mul_assoc]
  rfl
end Formalism.FourierDecayAlt.P.G7
