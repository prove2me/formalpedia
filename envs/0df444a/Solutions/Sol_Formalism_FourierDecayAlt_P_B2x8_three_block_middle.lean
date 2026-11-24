-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.three_block_middle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:49:32.31508+00:00
-- url     : https://prove2.me/submissions/7c6757fe-c83d-4bc8-9ca9-1dc832b527b6

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
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (a : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) (b : ℂ) : mid (mk3 k r' a y b) = y := by
  funext j
  have hj := j.isLt
  show mk3 k r' a y b (levPos k 1 r' j) = y j
  rw [three_block_apply]
  have c1 : ¬ ((levPos k 1 r' j).val = 0) := by simp only [levPos, Fin.val_mk]; omega
  have c2 : 1 ≤ (levPos k 1 r' j).val ∧ (levPos k 1 r' j).val < 2 * r' + k + 1 + 1 := by
    simp only [levPos, Fin.val_mk]; omega
  rw [if_neg c1, dif_pos c2]
  exact congrArg y (Fin.ext (by simp only [levPos, Fin.val_mk]; omega))
end Formalism.FourierDecayAlt.P.B2x8
