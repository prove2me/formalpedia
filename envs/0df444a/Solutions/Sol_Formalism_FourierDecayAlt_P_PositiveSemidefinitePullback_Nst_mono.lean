-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.Nst_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:47.977299+00:00
-- url     : https://prove2.me/submissions/a6846892-4217-4fa3-bead-9c579225808c

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_Nst_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
noncomputable section
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
theorem _root_.solution (D : Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε)
    (i s : ℕ) (w : W) (Y : Finset (Pt E)) {κ₁ κ₂ : Pt E → Pt E → ℂ}
    (hκ : PSDOn Y (fun h h' => κ₂ h h' - κ₁ h h')) (t : E) :
    (D.Nst ε i s w Y κ₁ t t).re ≤ (D.Nst ε i s w Y κ₂ t t).re := by
  have h := Nst_nonneg D hG hW hε i s w Y hκ t
  have e : D.Nst ε i s w Y (fun h h' => κ₂ h h' - κ₁ h h') t t =
      D.Nst ε i s w Y κ₂ t t - D.Nst ε i s w Y κ₁ t t := by
    simp only [Data.Nst, sub_mul, Finset.sum_sub_distrib, sub_div]
  rw [e, Complex.sub_re] at h
  linarith
end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
