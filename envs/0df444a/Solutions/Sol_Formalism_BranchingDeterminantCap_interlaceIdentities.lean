-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.interlaceIdentities
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:21.952812+00:00
-- url     : https://prove2.me/submissions/5373c5cc-a2fa-4e1b-867b-9d80e39971ec

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementR
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : InterlaceIdent := by
  intro n lam sg h
  have hsum : ∑ i, lam i = lam 0 + ∑ i : Fin n, lam i.succ := Fin.sum_univ_succ lam
  have hsum' : ∑ i, lam i = ∑ i : Fin n, lam i.castSucc + lam (Fin.last n) := Fin.sum_univ_castSucc lam
  have hd0 : d0 lam sg = ∑ i, sg i - ∑ i : Fin n, lam i.succ := by
    rw [d0, Finset.sum_sub_distrib]
  have hnn : ∀ i, 0 ≤ sg i - lam i.succ := fun i => by linarith [(h i).2]
  have h3 : 0 ≤ d0 lam sg := Finset.sum_nonneg fun i _ => hnn i
  have hle : ∀ i, sg i - lam i.succ ≤ d0 lam sg := fun i =>
    Finset.single_le_sum (f := fun i => sg i - lam i.succ) (fun j _ => hnn j) (Finset.mem_univ i)
  have h5 : ∀ i, sg i ∈ rset lam sg i := by
    intro i
    rw [rset, Finset.mem_Icc]
    have := (h i).1
    have := (h i).2
    have := hle i
    omega
  refine ⟨by linarith, ?_, h3, ?_, h5, ?_⟩
  · rw [Finset.sum_sub_distrib]; linarith
  · refine Finset.sum_nonneg fun i _ => ?_
    have := (h i).1
    have := (h i).2
    omega
  · intro i
    have hmem := h5 i
    rw [Finset.card_erase_of_mem hmem]
    rw [rset, Finset.mem_Icc] at hmem
    rw [rset, Int.card_Icc]
    have hc : 0 ≤ min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ := by omega
    have ht : ((min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ).toNat : ℤ) =
        min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ := Int.toNat_of_nonneg hc
    have h1 : 1 ≤ (min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ).toNat := by omega
    rw [Nat.cast_sub h1, ht]
    push_cast
    omega
end Formalism.BranchingDeterminantCap
