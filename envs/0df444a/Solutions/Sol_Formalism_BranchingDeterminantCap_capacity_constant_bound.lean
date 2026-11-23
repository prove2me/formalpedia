-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.capacity_constant_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:34:39.295687+00:00
-- url     : https://prove2.me/submissions/c3557a8d-72c6-435b-9353-81323c5f53b6

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
import Theorems.Thm_Formalism_BranchingDeterminantCap_cap_factor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace Formalism.BranchingDeterminantCap
private theorem d1_nonneg_of_interlace {n : ℕ} {lam : Fin (n + 1) → ℤ} {sg : Fin n → ℤ}
    (h : Interlace lam sg) : 0 ≤ d1 lam sg := by
  have hd0 : 0 ≤ d0 lam sg := by
    unfold d0; exact Finset.sum_nonneg (fun i _ => sub_nonneg.2 (h i).2)
  unfold d1
  exact Finset.sum_nonneg (fun i _ => le_min (by linarith [(h i).1, (h i).2]) hd0)
end Formalism.BranchingDeterminantCap
end

set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : CapConst := by
  unfold CapConst
  intro n lam sg h
  have hd0 : ∀ i : Fin n, sg i - lam i.succ ≤ d0 lam sg := by
    intro i; unfold d0
    exact Finset.single_le_sum (f := fun k : Fin n => sg k - lam k.succ)
      (fun k _ => sub_nonneg.2 (h k).2) (Finset.mem_univ i)
  have hd0nn : 0 ≤ d0 lam sg := by
    unfold d0; exact Finset.sum_nonneg (fun i _ => sub_nonneg.2 (h i).2)
  have hmem : ∀ i : Fin n, sg i ∈ rset lam sg i := by
    intro i; unfold rset; rw [Finset.mem_Icc]
    exact ⟨(h i).2, le_min (h i).1 (by linarith [hd0 i])⟩
  have hcard : ∀ i : Fin n, ((rset lam sg i).erase (sg i)).card =
      (min (lam i.castSucc - lam i.succ) (d0 lam sg)).toNat := by
    intro i
    rw [Finset.card_erase_of_mem (hmem i)]
    unfold rset
    rw [Int.card_Icc]
    have h1 := (h i).1
    have h2 := (h i).2
    have h3 := hd0 i
    omega
  have hm : ∀ i : Fin n, 0 ≤ min (lam i.castSucc - lam i.succ) (d0 lam sg) :=
    fun i => le_min (by linarith [(h i).1, (h i).2]) hd0nn
  have hd1nn : 0 ≤ d1 lam sg := d1_nonneg_of_interlace h
  have hsum : ∑ i : Fin n, ((rset lam sg i).erase (sg i)).card = (d1 lam sg).toNat := by
    rw [Finset.sum_congr rfl (fun i _ => hcard i)]
    have key : ((∑ i : Fin n, (min (lam i.castSucc - lam i.succ) (d0 lam sg)).toNat : ℕ) : ℤ) =
        (((d1 lam sg).toNat : ℕ) : ℤ) := by
      rw [Nat.cast_sum, Int.toNat_of_nonneg hd1nn,
        Finset.sum_congr rfl (fun i _ => Int.toNat_of_nonneg (hm i))]
      unfold d1
      rfl
    exact Nat.cast_injective key
  constructor
  · unfold cCap capEig
    rw [Finset.prod_ne_zero_iff]; intro i _
    rw [Finset.prod_ne_zero_iff]; intro v hv
    rw [Finset.prod_ne_zero_iff]; intro j _
    exact (cap_factor h i j v hv).1
  · unfold cCap capEig
    simp only [Finset.abs_prod]
    calc ∏ i : Fin n, ∏ v ∈ (rset lam sg i).erase (sg i), ∏ j : Fin n,
            |((v - (i : ℤ)) - (sg j - (j : ℤ)))|
        ≤ ∏ i : Fin n, ∏ v ∈ (rset lam sg i).erase (sg i), ∏ _j : Fin n,
            (lam 0 - lam (Fin.last n) + (n : ℤ) - 1) := by
          apply Finset.prod_le_prod
            (fun i _ => Finset.prod_nonneg (fun v _ => Finset.prod_nonneg (fun j _ => abs_nonneg _)))
          intro i _
          apply Finset.prod_le_prod (fun v _ => Finset.prod_nonneg (fun j _ => abs_nonneg _))
          intro v hv
          apply Finset.prod_le_prod (fun j _ => abs_nonneg _)
          intro j _
          exact (cap_factor h i j v hv).2
      _ = (lam 0 - lam (Fin.last n) + (n : ℤ) - 1) ^ (n * (d1 lam sg).toNat) := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [Finset.prod_pow_eq_pow_sum, ← pow_mul, hsum]
end Formalism.BranchingDeterminantCap
