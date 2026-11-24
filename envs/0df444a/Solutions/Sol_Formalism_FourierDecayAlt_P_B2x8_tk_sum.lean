-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.tk_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:19.611944+00:00
-- url     : https://prove2.me/submissions/7b59b7c4-32cb-4dad-aee1-5b95945993bd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_sum_split_first_middle_last

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
theorem _root_.solution (f : Fin (2 * (1 + r') + k + 1) → ℂ) :
    ∑ i, f i = f (tkF k r') + ∑ j, f (levPos k 1 r' j) + f (tkL k r') := by
  rw [sum_split_first_middle_last (n := 2 * r' + k + 1) (by omega) f]
  have h : (⟨2 * r' + k + 1 + 1, by omega⟩ : Fin (2 * (1 + r') + k + 1)) = tkL k r' :=
    Fin.ext (by simp only [tkL, Fin.val_mk]; omega)
  rw [h]
  try rfl
end Formalism.FourierDecayAlt.P.B2x8
