-- Prove2me | solution 1 for Formalism.ZF.lamF_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:43.818404+00:00
-- url     : https://prove2.me/submissions/480f4376-37a9-4219-9f3c-ad7e0e713017

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormLogDerivLeLamF
import Theorems.Thm_Formalism_ZF_term_vonMangoldt_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {σ : ℝ} (hσ : 1 < σ) : lamF σ = ‖L ↗Λ (σ : ℂ)‖ := by
  have h : L ↗Λ (σ : ℂ) = ((lamF σ : ℝ) : ℂ) := by
    rw [LSeries, lamF, Complex.ofReal_tsum]
    exact tsum_congr fun n => term_vonMangoldt_real σ n
  rw [h, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ lamF σ from tsum_nonneg fun n => norm_nonneg _)]
end Formalism.ZF
