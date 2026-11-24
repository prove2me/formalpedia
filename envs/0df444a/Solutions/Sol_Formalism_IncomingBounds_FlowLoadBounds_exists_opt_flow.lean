-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.exists_opt_flow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:47.621172+00:00
-- url     : https://prove2.me/submissions/71cade2e-0dcf-44b3-b53c-b6cdf6ec1c8b

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_continuous_load
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_continuous_flowVal
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_load_trunc
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_flowVal_trunc
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_trunc_nonneg
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_trunc_le
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_isCompact_box
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_mem_box
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
private theorem isFlow_zero_of_nonneg {D : ZMod d → ℝ} (hD : 0 ≤ D) : IsFlow l d D 0 := by
  unfold IsFlow
  exact ⟨fun s i => by simp, fun s => by simpa using hD s⟩
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
theorem _root_.solution (hl : 1 ≤ l) (D : ZMod d → ℝ) (hD : 0 ≤ D) :
    ∃ x, IsFlow l d D x ∧ ∀ y, IsFlow l d D y → flowVal d y ≤ flowVal d x := by
  have hclosed : IsClosed {x : ZMod d → ℕ → ℝ | IsFlow l d D x} := by
    have e : {x : ZMod d → ℕ → ℝ | IsFlow l d D x} =
        (⋂ s, ⋂ i, {x : ZMod d → ℕ → ℝ | 0 ≤ x s i}) ∩ ⋂ s, {x | dpLoad l d x s ≤ D s} := by
      ext x
      simp [IsFlow, dpLoad]
    rw [e]
    exact (isClosed_iInter fun s => isClosed_iInter fun i =>
      isClosed_le continuous_const
        (by fun_prop : Continuous fun x : ZMod d → ℕ → ℝ => x s i)).inter
      (isClosed_iInter fun s : ZMod d =>
        isClosed_le (continuous_load (l := l) (d := d) s) continuous_const)
  have hR : 0 ≤ ∑ s, D s := Finset.sum_nonneg fun s _ => hD s
  have hK : IsCompact (box d (∑ s, D s) ∩ {x | IsFlow l d D x}) :=
    (isCompact_box _).inter_right hclosed
  have h0 : (0 : ZMod d → ℕ → ℝ) ∈ box d (∑ s, D s) ∩ {x | IsFlow l d D x} :=
    ⟨mem_box.2 fun s i => ⟨by simp, by simpa using hR⟩, isFlow_zero_of_nonneg hD⟩
  obtain ⟨x, hxK, hxmax⟩ := hK.exists_isMaxOn ⟨0, h0⟩ continuous_flowVal.continuousOn
  refine ⟨x, hxK.2, fun y hy => ?_⟩
  have hyF : IsFlow l d D (trunc d y) := by
    unfold IsFlow
    exact ⟨trunc_nonneg hy.1, fun s => (load_trunc (l := l) y s).trans_le (hy.2 s)⟩
  have hyK : trunc d y ∈ box d (∑ s, D s) ∩ {x | IsFlow l d D x} :=
    ⟨mem_box.2 fun s i => ⟨trunc_nonneg hy.1 s i, trunc_le hl hy.1 hR
      (fun s => (hy.2 s).trans (Finset.single_le_sum (fun t _ => hD t) (Finset.mem_univ s))) s i⟩, hyF⟩
  calc Formalism.IncomingBounds.flowVal d y = Formalism.IncomingBounds.flowVal d (trunc d y) := (flowVal_trunc y).symm
    _ ≤ Formalism.IncomingBounds.flowVal d x := isMaxOn_iff.1 hxmax _ hyK
end Formalism.IncomingBounds.FlowLoadBounds
