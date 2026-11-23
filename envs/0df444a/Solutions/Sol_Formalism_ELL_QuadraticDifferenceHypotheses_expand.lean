-- Prove2me | solution 1 for Formalism.ELL.QuadraticDifferenceHypotheses.expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:54.900978+00:00
-- url     : https://prove2.me/submissions/0a3ea34b-65e5-43ea-8fa2-2981a3bd1f0b

import Definitions.Def_Formalism_EllipticTorsion_IsoExpand
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IsogenyExpansion
import Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_qd_comm
import Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_sum1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.ELL Formalism.ELL.QuadraticDifferenceHypotheses
universe u
variable {O M Q : Type u} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]
namespace Formalism.ELL.QuadraticDifferenceHypotheses
theorem _root_.solution {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    [LinearOrder ι] (s : Finset ι) (x : ι → M) :
    ψ (∑ e ∈ s, x e) = ∑ e ∈ s, ψ (x e) +
      ∑ e ∈ s, ∑ e' ∈ s.filter (fun e' => e < e'), quadDiff ψ (x e) (x e') := by
  refine Finset.induction_on_max s ?_ ?_
  · simp [H.zero]
  · intro a s hlt ih
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hdef : ∀ p q : M, ψ (p + q) = quadDiff ψ p q + ψ p + ψ q := by
      intro p q; unfold quadDiff; abel
    have hfa : (insert a s).filter (fun e' => a < e') = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact lt_irrefl _
      · exact not_lt.mpr (hlt z hz).le
    have hse : ∀ e ∈ s, ∑ e' ∈ (insert a s).filter (fun e' => e < e'), quadDiff ψ (x e) (x e') =
        quadDiff ψ (x e) (x a) + ∑ e' ∈ s.filter (fun e' => e < e'), quadDiff ψ (x e) (x e') := by
      intro e he
      rw [Finset.filter_insert, if_pos (hlt e he),
        Finset.sum_insert (fun h => ha (Finset.mem_filter.mp h).1)]
    rw [Finset.sum_insert ha, hdef, ih, Finset.sum_insert ha, Finset.sum_insert ha, hfa,
      Finset.sum_empty, Finset.sum_congr rfl hse, Finset.sum_add_distrib, qd_comm, sum1 H]
    abel
end Formalism.ELL.QuadraticDifferenceHypotheses
