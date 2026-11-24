-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.isClosed_K
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:49.127815+00:00
-- url     : https://prove2.me/submissions/1fb7a83d-0c32-4863-bca0-38fac6a14f8b

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
theorem _root_.solution (hl : 1 ≤ l) : IsClosed (Kset l d) := by
  refine IsSeqClosed.isClosed ?_
  intro q p hq hlim
  have hq' : ∀ n, ∃ x : ZMod d → ℕ → ℝ, (∀ s i, 0 ≤ x s i) ∧ (∀ s, dpLoad l d x s ≤ (q n).1 s) ∧
      (q n).2 ≤ Formalism.IncomingBounds.flowVal d x := fun n => mem_Kset_iff'.1 (hq n)
  choose x hxn hxl hxv using hq'
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto q hlim).exists_norm_le
  have hC' : ∀ n s, (q n).1 s ≤ C := fun n s => by
    have h1 : ‖(q n).1 s‖ ≤ C :=
      (norm_le_pi_norm (q n).1 s).trans ((norm_fst_le (q n)).trans (hC _ ⟨n, rfl⟩))
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans h1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ ⟨0, rfl⟩)
  have hy : ∀ n, trunc d (x n) ∈ box d C := fun n => mem_box.2 fun s i =>
    ⟨trunc_nonneg (hxn n) s i,
      trunc_le hl (hxn n) hC0 (fun s => (hxl n s).trans (hC' n s)) s i⟩
  obtain ⟨z, hz, φ, hφ, hzlim⟩ := (isCompact_box C).tendsto_subseq hy
  have hqφ : Filter.Tendsto (q ∘ φ) Filter.atTop (nhds p) := hlim.comp hφ.tendsto_atTop
  refine mem_Kset_iff'.2 ⟨z, fun s i => ((mem_box.1 hz) s i).1, fun s => ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun n => dpLoad l d (trunc d (x (φ n))) s) Filter.atTop
        (nhds (dpLoad l d z s)) := ((continuous_load (l := l) s).tendsto z).comp hzlim
    have h2 : Filter.Tendsto (fun n => (q (φ n)).1 s) Filter.atTop (nhds (p.1 s)) :=
      (((continuous_apply s).comp continuous_fst).tendsto p).comp hqφ
    exact le_of_tendsto_of_tendsto' h1 h2 fun n =>
      (load_trunc (l := l) (x (φ n)) s).trans_le (hxl (φ n) s)
  · have h1 : Filter.Tendsto (fun n => (q (φ n)).2) Filter.atTop (nhds p.2) :=
      (continuous_snd.tendsto p).comp hqφ
    have h2 : Filter.Tendsto (fun n => Formalism.IncomingBounds.flowVal d (trunc d (x (φ n)))) Filter.atTop
        (nhds (Formalism.IncomingBounds.flowVal d z)) := (continuous_flowVal.tendsto z).comp hzlim
    exact le_of_tendsto_of_tendsto' h1 h2 fun n =>
      (hxv (φ n)).trans (flowVal_trunc (x (φ n))).ge
end Formalism.IncomingBounds.FlowLoadBounds
