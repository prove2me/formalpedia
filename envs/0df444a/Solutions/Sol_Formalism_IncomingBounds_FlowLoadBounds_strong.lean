-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.strong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:54:53.439934+00:00
-- url     : https://prove2.me/submissions/16ee95e7-7a10-408e-9096-6b2de54d1cfd

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_weak_core
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_exists_opt_flow
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_maxFlow_eq
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_exists_dual_lt
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_clip_dual
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_isCompact_dual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set
open scoped Pointwise
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowLoadBounds
variable {l d : ℕ} [NeZero d]
namespace Formalism.IncomingBounds.FlowLoadBounds
theorem _root_.solution (hl : 1 ≤ l) (D : ZMod d → ℝ) (hD : 0 ≤ D) :
    ∃ sig, IsDual l d sig ∧ ∑ s, D s * sig s = maxFlow l d D := by
  obtain ⟨x, hx, hmax⟩ := exists_opt_flow hl D hD
  rw [maxFlow_eq hx hmax]
  have hone : (fun _ => (1 : ℝ)) ∈ {sig : ZMod d → ℝ | Formalism.IncomingBounds.IsDual l d sig} := by
    show Formalism.IncomingBounds.IsDual l d (fun _ => (1 : ℝ))
    refine ⟨fun s => ⟨zero_le_one, le_rfl⟩, fun s i _ => ?_⟩
    show 1 ≤ (l : ℝ) ^ i * 1 + 1
    have : (0 : ℝ) ≤ (l : ℝ) ^ i := by positivity
    linarith
  obtain ⟨σ, hσ, hmin⟩ := (isCompact_dual (l := l) (d := d)).exists_isMinOn ⟨_, hone⟩
    (by fun_prop : Continuous fun σ : ZMod d → ℝ => ∑ s, D s * σ s).continuousOn
  have hσ' : Formalism.IncomingBounds.IsDual l d σ := hσ
  refine ⟨σ, hσ', le_antisymm ?_ (weak_core hx (fun s => (hσ'.1 s).1) hσ'.2)⟩
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨τ, h0, h1, hlt⟩ := exists_dual_lt hl D hD (fun y hy => hmax y hy) hε
  have hfeas := clip_dual hl h0 h1
  have h2 : ∑ s, D s * σ s ≤ ∑ s, D s * min (τ s) 1 := isMinOn_iff.1 hmin _ hfeas
  have h3 : ∑ s, D s * min (τ s) 1 ≤ ∑ s, D s * τ s :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hD s)
  linarith
end Formalism.IncomingBounds.FlowLoadBounds
