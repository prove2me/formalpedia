-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.mid_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:47:57.617429+00:00
-- url     : https://prove2.me/submissions/895ed9d0-7355-4827-ad17-d00b45b13deb

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_mid_levPos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mid_levPos


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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) : mid k r' p ↔ p ∈ Set.range (levPos k 1 r') := by
  constructor
  · intro h
    have h' : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 := h
    refine ⟨⟨p.val - 1, by omega⟩, Fin.ext ?_⟩
    show p.val - 1 + 1 = p.val
    omega
  · rintro ⟨s, rfl⟩
    exact mid_levPos k r' s
end Formalism.FourierDecayAlt.P.LongWeylElement
