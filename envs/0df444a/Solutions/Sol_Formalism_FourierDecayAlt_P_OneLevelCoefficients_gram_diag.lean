-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OneLevelCoefficients.gram_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:22.433552+00:00
-- url     : https://prove2.me/submissions/bdea7702-b3a1-48d8-ac1d-e6edbbde771b

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
theorem _root_.solution (D : Data E W) (hG : D.GramPSD) (ε : ℝ) (hε : 0 < ε) (i : ℕ) (w : W) (p : Pt E) :
    0 ≤ (D.gram ε i w p p).re := by
  have h := hG ε hε i w {p}
  have := Matrix.PosSemidef.diag_nonneg h (i := ⟨p, by simp⟩)
  have h2 : 0 ≤ D.gram ε i w p p := by simpa using this
  exact (Complex.le_def.1 h2).1
end Formalism.FourierDecayAlt.P.OneLevelCoefficients
