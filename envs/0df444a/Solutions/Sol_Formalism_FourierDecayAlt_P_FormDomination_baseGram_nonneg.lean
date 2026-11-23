-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FormDomination.baseGram_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:51.14679+00:00
-- url     : https://prove2.me/submissions/2d53d8c3-88bd-4ed8-82dc-8e9ab279d8f3

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_form_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FormDomination
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
variable {E W : Type} [Field E] (D : Data E W)
namespace Formalism.FourierDecayAlt.P.FormDomination
theorem _root_.solution (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ :=
  div_nonneg (form_nonneg Y κ _ hκ (hG ε hε k w Y)) (hW w).le
end Formalism.FourierDecayAlt.P.FormDomination
