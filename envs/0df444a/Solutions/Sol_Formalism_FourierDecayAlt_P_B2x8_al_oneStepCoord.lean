-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.al_oneStepCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:00.874251+00:00
-- url     : https://prove2.me/submissions/1d8365bd-bfb6-4b79-8c66-a991933c9937

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_oneStep_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_oneStep_exists

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
theorem _root_.solution : OneStepCoord := by
  intro k r' g hg hc
  obtain ⟨x, g₁, x', hg₁, he⟩ := al_oneStep_exists hg hc
  refine ⟨(x, g₁, x'), ⟨hg₁, he⟩, ?_⟩
  rintro ⟨z, h₁, z'⟩ ⟨-, hz⟩
  simp only at hz
  obtain ⟨e1, e2, e3⟩ := al_oneStep_inj hc (hz.symm.trans he)
  rw [e1, e2, e3]
end Formalism.FourierDecayAlt.P.B2x8
