-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OneLevelCoefficients.X0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:33.674902+00:00
-- url     : https://prove2.me/submissions/ebca024b-5ceb-41f2-8f65-656e1ac50a15

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OneLevelCoefficients
open Formalism.FourierDecayAlt.TB Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.OneLevelCoefficients
theorem _root_.solution (T : Tower E) : T.X 0 = {[]} := by
  ext p
  rw [T.isTower 0 p, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hb⟩
    cases p with
    | nil => rfl
    | cons a q =>
      have := (hb 0 (by simp)).1
      simp [level] at hl
      simp at this
      omega
  · rintro rfl
    simp [level]
end Formalism.FourierDecayAlt.P.OneLevelCoefficients
