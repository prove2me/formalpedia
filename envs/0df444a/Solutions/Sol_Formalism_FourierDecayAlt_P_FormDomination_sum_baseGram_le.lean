-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FormDomination.sum_baseGram_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:23.145198+00:00
-- url     : https://prove2.me/submissions/82f70ed7-72ac-49db-aa79-459a152bda36

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_form_dom

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
    (Y : Finset (Pt E)) (R : Finset E) (c : ℝ) (κ : Pt E → Pt E → ℂ)
    (Th : E → Pt E → Pt E → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * κ a b - ∑ t ∈ R, Th t a b)) :
    ∑ t ∈ R, D.N0 ε k w Y (Th t) ≤ c * D.N0 ε k w Y κ := by
  unfold Data.N0
  rw [← Finset.sum_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (form_dom Y R c κ _ Th h (hG ε hε k w Y)) (hW w).le
end Formalism.FourierDecayAlt.P.FormDomination
