-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.not_mid_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:47:29.714238+00:00
-- url     : https://prove2.me/submissions/34e81d2a-1c36-4edc-a563-dca6a117ec2e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution (i : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) : ∃ a : Fin r, i = eI k r a ∨ i = esI k r a := by
  have := i.isLt
  by_cases h : i.val < r
  · exact ⟨⟨i.val, h⟩, Or.inl rfl⟩
  · refine ⟨⟨2 * r + k - i.val, by omega⟩, Or.inr ?_⟩
    apply Fin.ext
    simp only [esI]
    omega
end Formalism.FourierDecayAlt.P.B2x3
