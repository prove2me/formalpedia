-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.absorb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:04.357984+00:00
-- url     : https://prove2.me/submissions/e0383840-1d75-4b00-8146-a3860e639a15

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : Absorb := by
  intro B S σ ε A hL hb h
  have hne : (S.Eset ε σ).Nonempty := ⟨_, S.a, ⟨le_refl _, by linarith⟩, rfl⟩
  have : S.Esup ε σ ≤ A + S.Esup ε σ / 2 := by
    apply csSup_le hne
    rintro _ ⟨Y, hY, rfl⟩
    exact h Y hY
  linarith
end Formalism.FourierDecayAlt.P.LEx1
