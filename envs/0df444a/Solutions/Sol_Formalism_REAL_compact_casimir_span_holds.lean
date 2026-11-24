-- Prove2me | solution 1 for Formalism.REAL.compact_casimir_span_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:57:38.811697+00:00
-- url     : https://prove2.me/submissions/7a62099b-9f8c-4ca5-8c1a-87527cf9d26d

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_compact_span_le_stable
import Theorems.Thm_Formalism_REAL_compact_lie_commute_casimir
import Theorems.Thm_Formalism_REAL_compact_casimir_highest_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : KCasSpan := by
  intro V _ _ n ε F μ x h hx y hy
  have hS : kSpan ε F x ≤ (CasK ε F).eigenspace ((ckv ε μ : ℝ) : ℂ) := by
    apply compact_span_le_stable
    · rw [Module.End.mem_eigenspace_iff]; exact compact_casimir_highest_weight h hx
    · intro a b hab z hz
      rw [Module.End.mem_eigenspace_iff] at hz ⊢
      have := LinearMap.congr_fun (compact_lie_commute_casimir h hab) z
      simp only [Module.End.mul_apply] at this
      rw [← this, hz, map_smul]
  exact Module.End.mem_eigenspace_iff.mp (hS hy)
end Formalism.REAL
