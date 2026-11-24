-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x6.cases3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:15:43.481339+00:00
-- url     : https://prove2.me/submissions/2c993822-f734-42f4-b489-71e75275683b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_iL_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lv_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_iL_val


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x6
theorem _root_.solution (p : Fin (2 * (1 + r') + k + 1)) : p = iF k r' ∨ p = iL k r' ∨ ∃ j, p = lv k r' j := by
  by_cases h0 : p.val = 0
  · left; exact Fin.ext (by rw [iF_val]; exact h0)
  by_cases h1 : p.val = 2 * (1 + r') + k
  · right; left; exact Fin.ext (by rw [iL_val]; exact h1)
  · right; right
    have := p.isLt
    exact ⟨⟨p.val - 1, by omega⟩, Fin.ext (by rw [lv_val]; simp only; omega)⟩
end Formalism.FourierDecayAlt.P.B2x6
