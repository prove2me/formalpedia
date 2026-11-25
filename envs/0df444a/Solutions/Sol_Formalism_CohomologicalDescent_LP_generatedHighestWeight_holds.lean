-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LP.generatedHighestWeight_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:23:51.152228+00:00
-- url     : https://prove2.me/submissions/8de299d2-bc2b-4777-a3e1-f84f36c236d3

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLP
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_GeneratedHighestWeightHolds
import Theorems.Thm_Formalism_CohomologicalDescent_LP_lowSpan_stab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LP
open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample
namespace Formalism.CohomologicalDescent.LP
theorem _root_.solution : GeneratedHW := by
  intro K N q _ _ _ _ _ T B hF κ hgen v μ hv hhw
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ κ a := by
    by_contra hcon
    exact hne (funext fun a => by_contra fun h => hcon ⟨a, h⟩)
  have htop : lowSpan T κ = ⊤ :=
    hgen _ (lowSpan_stab T hF.gl κ) (fun w hw => Submodule.subset_span (LowW.base w hw))
  have horth : ∀ x, LowW T κ x → B v x = 0 := by
    intro x hx
    cases hx with
    | base _ hw =>
      have h := hF.adj a a v x
      rw [hhw.2 a, hw.2 a, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h
      have h2 : (μ a - κ a) * B v x = 0 := by rw [sub_mul, h, sub_self]
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)
    | step c d y hdc _ =>
      rw [← hF.adj d c v y, hhw.1 d c hdc, map_zero, LinearMap.zero_apply]
  have hall : ∀ y ∈ lowSpan T κ, B v y = 0 := by
    intro y hy
    have : lowSpan T κ ≤ LinearMap.ker (B v) := by
      rw [lowSpan, Submodule.span_le]
      intro x hx
      exact LinearMap.mem_ker.2 (horth x hx)
    exact LinearMap.mem_ker.1 (this hy)
  have h0 : B v v = 0 := hall v (by rw [htop]; exact Submodule.mem_top)
  exact absurd (hF.pos v hv) (by rw [h0]; exact lt_irrefl _)
end Formalism.CohomologicalDescent.LP
