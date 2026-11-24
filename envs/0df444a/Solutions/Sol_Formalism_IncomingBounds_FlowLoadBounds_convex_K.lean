-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.convex_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:13.267401+00:00
-- url     : https://prove2.me/submissions/5ed15a55-9784-4347-8585-b904130b7620

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_load_comb
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_flowVal_comb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Set
open scoped Pointwise
namespace Formalism.IncomingBounds
namespace FlowLoadBounds
variable {l d : ℕ} [NeZero d]
private theorem mem_Kset_iff' {q : (ZMod d → ℝ) × ℝ} :
    q ∈ Kset l d ↔ ∃ x : ZMod d → ℕ → ℝ, (∀ s i, 0 ≤ x s i) ∧
      (∀ s, dpLoad l d x s ≤ q.1 s) ∧ q.2 ≤ Formalism.IncomingBounds.flowVal d x := Iff.rfl
end FlowLoadBounds
open FlowLoadBounds
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set
open scoped Pointwise
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowLoadBounds
variable {l d : ℕ} [NeZero d]
namespace Formalism.IncomingBounds.FlowLoadBounds
theorem _root_.solution : Convex ℝ (Kset l d) := by
  intro q1 hq1 q2 hq2 a b ha hb hab
  obtain ⟨x1, h1n, h1l, h1v⟩ := mem_Kset_iff'.1 hq1
  obtain ⟨x2, h2n, h2l, h2v⟩ := mem_Kset_iff'.1 hq2
  refine mem_Kset_iff'.2 ⟨fun s i => a * x1 s i + b * x2 s i,
    fun s i => add_nonneg (mul_nonneg ha (h1n s i)) (mul_nonneg hb (h2n s i)), fun s => ?_, ?_⟩
  · rw [load_comb]
    simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (h1l s) ha) (mul_le_mul_of_nonneg_left (h2l s) hb)
  · rw [flowVal_comb]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left h1v ha) (mul_le_mul_of_nonneg_left h2v hb)
end Formalism.IncomingBounds.FlowLoadBounds
