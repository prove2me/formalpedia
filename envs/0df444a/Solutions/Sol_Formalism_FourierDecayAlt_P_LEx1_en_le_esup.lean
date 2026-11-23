-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.en_le_esup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:30.798352+00:00
-- url     : https://prove2.me/submissions/c6bdcf3b-49bd-40c7-80b9-f6fbe3ef7d4d

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
theorem _root_.solution {B : Base} (S : Step B) (ε σ : ℝ) (hb : BddAbove (S.Eset ε σ)) (hP : S.PReg) (Y : ℝ) (hY : Y ∈ S.J) :
    S.En ε σ Y ≤ S.Esup ε σ * |S.P Y| := by
  have h1 : S.En ε σ Y / |S.P Y| ≤ S.Esup ε σ := le_csSup hb ⟨Y, hY, rfl⟩
  have hpos : 0 < |S.P Y| := abs_pos.mpr (hP.2 Y hY)
  rwa [div_le_iff₀ hpos] at h1
end Formalism.FourierDecayAlt.P.LEx1
