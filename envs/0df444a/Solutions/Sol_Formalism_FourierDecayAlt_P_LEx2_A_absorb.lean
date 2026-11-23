-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.A.absorb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:32.08936+00:00
-- url     : https://prove2.me/submissions/b80b4d78-f572-4f9d-af3f-3c5a46a24eef

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2 Formalism.FourierDecayAlt.P.LEx2.A
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx2.A
theorem _root_.solution : Absorb := by
  intro B S σ ε A hL hb h
  have hne : (S.Eset ε σ).Nonempty := ⟨_, S.a, ⟨le_refl _, by linarith⟩, rfl⟩
  have : S.Esup ε σ ≤ A + S.Esup ε σ / 2 := by
    apply csSup_le hne
    rintro _ ⟨Y, hY, rfl⟩
    exact h Y hY
  linarith
end Formalism.FourierDecayAlt.P.LEx2.A
