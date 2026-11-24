-- Prove2me | solution 1 for Formalism.ZF.perron_norm_LSeries_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:43:08.371198+00:00
-- url     : https://prove2.me/submissions/9b5f838c-0ed2-46c1-aabe-c07abcd390e8

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {σ₀ : ℝ} (hσ : 1 < σ₀) (w : ℂ) (hw : w.re = σ₀) :
    ‖LSeries ↗Λ w‖ ≤ ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by
  have hs : LSeriesSummable ↗Λ (σ₀ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have heq : ∀ n, ‖LSeries.term ↗Λ w n‖ = ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by
    intro n
    simp [LSeries.norm_term_eq, hw]
  unfold LSeries
  calc ‖∑' n, LSeries.term ↗Λ w n‖ ≤ ∑' n, ‖LSeries.term ↗Λ w n‖ :=
        norm_tsum_le_tsum_norm (hs.norm.congr fun n => (heq n).symm)
    _ = ∑' n, ‖LSeries.term ↗Λ (σ₀ : ℂ) n‖ := by simp_rw [heq]
end Formalism.ZF
