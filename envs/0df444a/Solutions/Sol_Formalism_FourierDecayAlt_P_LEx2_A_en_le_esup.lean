-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.A.en_le_esup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:32.350853+00:00
-- url     : https://prove2.me/submissions/bc91649c-f513-4141-927e-06cd3f351502

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
theorem _root_.solution {B : Base} (S : Step B) (ε σ : ℝ) (hb : BddAbove (S.Eset ε σ)) (hP : S.PReg) (Y : ℝ) (hY : Y ∈ S.J) :
    S.En ε σ Y ≤ S.Esup ε σ * |S.P Y| := by
  have h1 : S.En ε σ Y / |S.P Y| ≤ S.Esup ε σ := le_csSup hb ⟨Y, hY, rfl⟩
  have hpos : 0 < |S.P Y| := abs_pos.mpr (hP.2 Y hY)
  rwa [div_le_iff₀ hpos] at h1
end Formalism.FourierDecayAlt.P.LEx2.A
