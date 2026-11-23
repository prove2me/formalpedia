-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.Nst_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:24.892799+00:00
-- url     : https://prove2.me/submissions/c2a46ec5-c0b7-405c-90f1-08c01bc14cd4

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_psd_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_psd_pull
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_psd_sum_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefinitePullback_Nst_re

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
    (i s : ℕ) (w : W) (Y : Finset (Pt E)) {κ : Pt E → Pt E → ℂ} (hκ : PSDOn Y κ) (t : E) :
    0 ≤ (D.Nst ε i s w Y κ t t).re := by
  rw [Nst_re]
  refine div_nonneg ?_ (hW w).le
  exact psd_sum_nonneg (psd_mul hκ (psd_pull (fun h => join h s t) (hG ε hε i w _)))
end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
