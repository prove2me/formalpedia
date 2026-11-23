-- Prove2me | solution 1 for Formalism.ExtensionFiltration.bad_part_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:47.873289+00:00
-- url     : https://prove2.me/submissions/f8b111e0-d975-49ca-9c6f-3b8b794b75f5

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_StatementA
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.ExtensionFiltration
namespace Formalism.ExtensionFiltration
theorem _root_.solution : BadRowsNumeric := by
  intro d dg db muN muG mmax G Q δ hd hsum hdb hdb3 hδ hδ12 hdeg hmuN hmm hG
  have hQ : 0 ≤ Q := le_trans (abs_nonneg _) hmuN
  have hN1 : -Q ≤ muN := by have := neg_abs_le muN; linarith
  have hdg : 3 / 4 * d ≤ dg := by nlinarith
  have hdg0 : 0 < dg := by linarith
  by_contra hcon
  rw [not_le] at hcon
  have h1 : dg * muG < dg * (muN - 12 * δ * Q) := mul_lt_mul_of_pos_left hcon hdg0
  have h2 : db * (mmax + G) ≤ db * (2 * Q) := by
    apply mul_le_mul_of_nonneg_left _ hdb; linarith
  have h3 : db * (-muN) ≤ db * Q := by
    apply mul_le_mul_of_nonneg_left _ hdb; linarith
  have h4 : db * Q ≤ 3 * δ * d * Q := mul_le_mul_of_nonneg_right hdb3 hQ
  have h5 : 3 / 4 * d * (δ * Q) ≤ dg * (δ * Q) :=
    mul_le_mul_of_nonneg_right hdg (mul_nonneg hδ hQ)
  subst hsum
  nlinarith
end Formalism.ExtensionFiltration
