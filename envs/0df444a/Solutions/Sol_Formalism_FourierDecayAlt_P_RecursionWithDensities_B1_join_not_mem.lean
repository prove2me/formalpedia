-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.B1.join_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:40.190811+00:00
-- url     : https://prove2.me/submissions/e99463f5-216e-4e3b-8220-3837f9498241

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.TC
open scoped ComplexOrder
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
theorem _root_.solution (T : Tower E) {i s : ℕ} {t : E}
    (ht : t ∉ T.Sg (i - s + 1) s) (h : Pt E) : join h s t ∉ T.X i := by
  intro hm
  rw [T.isTower i] at hm
  obtain ⟨hl, hk⟩ := hm
  have hl' : level h + s = i := by simpa [level, join] using hl
  have hk2 : h.length < (join h s t).length := by simp [join]
  have := (hk h.length hk2).2
  have e1 : (join h s t)[h.length]'hk2 = (s, t) := by simp [join]
  have e2 : blockStart (join h s t) h.length = level h + 1 := by
    simp [blockStart, join, level, List.take_append_of_le_length (le_refl h.length)]
  rw [e1, e2] at this
  have e3 : level h = i - s := by omega
  rw [e3] at this
  exact ht this
end Formalism.FourierDecayAlt.P.RecursionWithDensities.B1
