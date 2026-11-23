-- Prove2me | solution 1 for Formalism.ExtensionFiltration.descent_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:39:47.000419+00:00
-- url     : https://prove2.me/submissions/3e8f57b6-9f6d-491b-bcc7-5acd8afca5fd

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
theorem _root_.solution : DescentNumeric := by
  intro dA dB muA muN cfl X P Λ Q ε hdA hAB hBε hε hX hP hdeg hmuA hcfl hΛ
  have hdB : 0 < dB := lt_of_lt_of_le hdA hAB
  have hQ : 0 ≤ Q := le_trans (abs_nonneg _) hcfl
  have hc1 : cfl ≤ Q := le_trans (le_abs_self _) hcfl

  by_contra hcon
  rw [not_le] at hcon
  have h1 : dB * muN < dB * (cfl - X - P - 2 * ε * Q) := mul_lt_mul_of_pos_left hcon hdB
  have h2 : dA * (cfl - X - P) ≤ dA * (muA - P) := by
    apply mul_le_mul_of_nonneg_left _ hdA.le; linarith
  have h3 : (dB - dA) * (-Q) ≤ (dB - dA) * (-Λ) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
  have h4 : (dB - dA) * (cfl - X - P) ≤ (dB - dA) * Q := by
    apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
  have h5 : (dB - dA) * Q ≤ ε * dB * Q := by
    apply mul_le_mul_of_nonneg_right _ hQ; linarith
  nlinarith
end Formalism.ExtensionFiltration
