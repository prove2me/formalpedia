-- Prove2me | solution 1 for Formalism.ELL.QuadraticDifferenceHypotheses.expand_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:20.783027+00:00
-- url     : https://prove2.me/submissions/41234ed2-aa0b-4651-b139-6c84a71b1d72

import Definitions.Def_Formalism_EllipticTorsion_IsoExpand
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IsogenyExpansion
import Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_sum2
import Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_expand
import Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_mk_quadDiff
import Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_biHyp_of
import Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_mk_nrm

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
variable {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T]
namespace Formalism.ELL.QuadraticDifferenceHypotheses
theorem _root_.solution {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M) :
    QuotientAddGroup.mk' N (∑ i, φ (∑ e, y e i • t e)) =
      QuotientAddGroup.mk' N ((∑ e, (∑ i, nrm (y e i)) • φ (t e))
        + (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
            quadDiff φ (t e) ((∑ i, bar (y e i) * y e' i) • t e'))) := by
  set f := QuotientAddGroup.mk' N
  have H := biHyp_of h
  have e1 : ∀ i, f (φ (∑ e, y e i • t e)) = ∑ e, f (nrm (y e i) • φ (t e)) +
      ∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
        quadDiff (fun a => f (φ a)) (t e) ((bar (y e i) * y e' i) • t e') := by
    intro i
    rw [expand H]
    congr 1
    · exact Finset.sum_congr rfl fun e _ => mk_nrm h _ _
    · refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
      rw [H.adj, smul_smul]
  rw [map_sum, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, map_add, map_sum,
    map_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← map_sum, ← Finset.sum_smul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_comm, map_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    rw [mk_quadDiff, Finset.sum_smul, sum2 H]
end Formalism.ELL.QuadraticDifferenceHypotheses
