-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.edgeSum_elM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:52.382937+00:00
-- url     : https://prove2.me/submissions/c7bfe38f-cb85-4121-8656-05a662bad5ad

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset Matrix
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K : Type} [Field K] {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (p q : Fin N) (v : K) :
    edgeSum (elM p q v) = if (q : ℕ) = p + 1 then v else 0 := by
  unfold edgeSum
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single q]
    · by_cases h : (q : ℕ) = p + 1
      · have hpq : p ≠ q := by intro h'; rw [h'] at h; omega
        simp [h, elM, Matrix.one_apply_ne hpq]
      · simp [h]
    · intro c _ hc
      split_ifs with h
      · have hpc : p ≠ c := by intro h'; rw [h'] at h; omega
        simp [elM, Matrix.one_apply_ne hpc, hc]
      · rfl
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · intro x _ hx
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs with h
    · have hxc : x ≠ c := by intro h'; rw [h'] at h; omega
      simp [elM, Matrix.one_apply_ne hxc, hx]
    · rfl
  · intro h'; exact absurd (Finset.mem_univ _) h'
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
