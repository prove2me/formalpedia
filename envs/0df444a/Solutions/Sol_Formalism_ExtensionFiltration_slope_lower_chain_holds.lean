-- Prove2me | solution 1 for Formalism.ExtensionFiltration.slope_lower_chain_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:14.602799+00:00
-- url     : https://prove2.me/submissions/f17abf63-0fef-4497-be38-9f6dcbf33211

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_StatementA
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Theorems.Thm_Formalism_ExtensionFiltration_descent_numeric
import Theorems.Thm_Formalism_ExtensionFiltration_bad_part_numeric

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
theorem _root_.solution : SlopeLowerChain := by
  intro Pl _ w c1 ua muU muA muN muG muM mmax dA dB d dg db C1 Cf LL0 L b rd m q' cfl ε δ Q P Λ G P9
    h41 hcfl hfl hdA hAB hBε hε hP hdesc hcQ hΛ hεQ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG h9 hsmall
    hC1 hCf hq0 hqm hw hua hrd0 hrdL hLL hU hb
  have hLL0 : 0 ≤ LL0 := le_trans hrd0 hrdL
  have hU0 : 0 ≤ ∑ τ, ua τ := by linarith
  have hX : 0 ≤ 2 * (C1 * LL0 * (∑ τ, ua τ) + b / 4) := by positivity
  have hN := descent_numeric dA dB muA muN (2 * cfl) (2 * (C1 * LL0 * (∑ τ, ua τ) + b / 4)) P Λ Q ε
    hdA hAB hBε hε hX hP hdesc (by linarith) hcQ hΛ
  have hGd := bad_part_numeric d dg db muN muG mmax G Q δ hd hsum hdb hdb3 hδ hδ12 hcut hmuN hmm hG
  have hW0 : 0 ≤ ∑ τ, w τ := Finset.sum_nonneg (fun τ _ => hw τ)
  have hmW : m * (∑ τ, w τ) ≤ 2 * ∑ τ, ua τ := by
    have : ∑ τ, m * w τ / 2 ≤ ∑ τ, ua τ := Finset.sum_le_sum (fun τ _ => hua τ)
    rw [← Finset.sum_div, ← Finset.mul_sum] at this
    linarith
  have hqW : q' * (∑ τ, w τ) ≤ 2 * ∑ τ, ua τ :=
    le_trans (mul_le_mul_of_nonneg_right hqm hW0) hmW
  have h1 : Real.log rd * (q' * (∑ τ, w τ)) ≤ LL0 * (2 * ∑ τ, ua τ) :=
    mul_le_mul hrdL hqW (mul_nonneg hq0 hW0) hLL0
  have h2 : L ≤ LL0 * (∑ τ, ua τ) := by nlinarith
  have h3 : Cf * (Real.log rd * (q' * (∑ τ, w τ))) ≤ Cf * (LL0 * (2 * ∑ τ, ua τ)) :=
    mul_le_mul_of_nonneg_left h1 hCf
  have h4 : Cf * L ≤ Cf * (LL0 * (∑ τ, ua τ)) := mul_le_mul_of_nonneg_left h2 hCf
  nlinarith
end Formalism.ExtensionFiltration
