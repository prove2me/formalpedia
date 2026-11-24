-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:19:50.566649+00:00
-- url     : https://prove2.me/submissions/a00b2f72-5534-4e23-9f1a-d020cf8d6bee

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mid_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_out

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : jV k r (wbPart k r v) = v := by
  funext i
  by_cases hi : mid k r i
  · obtain ⟨a, rfl⟩ := mid_exists hi
    rw [jV_wI]; rfl
  · rw [jV_out _ hi, hv i (by have := hi; omega)]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
