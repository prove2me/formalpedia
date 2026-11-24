-- Prove2me | solution 1 for Formalism.REAL.compact_casimir_highest_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:44:10.437431+00:00
-- url     : https://prove2.me/submissions/8bcc1dea-facf-4e65-b87b-7d5f6a23089c

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_compact_casimir_apply
import Theorems.Thm_Formalism_REAL_compact_casimir_term_highest
import Theorems.Thm_Formalism_REAL_compact_casimir_value_eq

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x) :
    CasK ε F x = ((ckv ε μ : ℝ) : ℂ) • x := by
  rw [compact_casimir_apply, ← compact_casimir_value_eq μ]
  have : ∀ a b, (if ε a = ε b then F a b (F b a x) else 0) =
      (((if ε a = ε b then (if a = b then μ a ^ 2 else if a < b then μ a - μ b else 0) else 0 : ℝ))
        : ℂ) • x := by
    intro a b
    by_cases hab : ε a = ε b
    · rw [if_pos hab, if_pos hab, compact_casimir_term_highest h hx hab]
    · simp [hab]
  simp_rw [this, ← Finset.sum_smul]
  push_cast
  rfl
end Formalism.REAL
