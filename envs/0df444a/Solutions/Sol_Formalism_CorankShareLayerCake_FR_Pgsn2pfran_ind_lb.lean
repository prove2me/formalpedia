-- Prove2me | solution 1 for Formalism.CorankShareLayerCake.FR.Pgsn2pfran.ind_lb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:34.537414+00:00
-- url     : https://prove2.me/submissions/e09d7c65-d4f2-473d-9ae1-381ec04e89b3

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_LayerCakeFormula
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfran_ind_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CorankShareLayerCake Formalism.CorankShareLayerCake.FR
open Finset MeasureTheory
open Formalism.CorankShareLayerCake.FR.Pgsn2pfran
namespace Formalism.CorankShareLayerCake.FR.Pgsn2pfran
theorem _root_.solution (a xj HH : ℝ) (h : a - HH ≤ xj) (hHH : 0 ≤ HH) :
    a - xj ≤ ∫ τ in (0:ℝ)..HH, (if τ < a - xj then (1:ℝ) else 0) := by
  rcases le_total (a - xj) 0 with h0 | h0
  · have hpos : 0 ≤ ∫ τ in (0:ℝ)..HH, (if τ < a - xj then (1:ℝ) else 0) := by
      apply intervalIntegral.integral_nonneg hHH
      intro u _
      split_ifs <;> norm_num
    linarith
  · exact le_of_eq (ind_int (a - xj) HH h0 (by linarith)).symm
end Formalism.CorankShareLayerCake.FR.Pgsn2pfran
