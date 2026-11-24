-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.idx_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:03:09.944216+00:00
-- url     : https://prove2.me/submissions/5ae1a1c4-26f4-4e25-b406-27053cf6f1eb

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_iL_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_lev_val

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) :
    p = i0 k r' ∨ (∃ j, p = levPos k 1 r' j) ∨ p = iL k r' := by
  have hp := p.isLt
  by_cases h0 : p.val = 0
  · exact Or.inl (Fin.ext h0)
  by_cases hL : p.val = 2 * r' + k + 2
  · exact Or.inr (Or.inr (Fin.ext (by rw [hL, iL_val])))
  · refine Or.inr (Or.inl ⟨⟨p.val - 1, by omega⟩, Fin.ext ?_⟩)
    rw [lev_val]
    show p.val = p.val - 1 + 1
    omega
end Formalism.FourierDecayAlt.P.B2x5
