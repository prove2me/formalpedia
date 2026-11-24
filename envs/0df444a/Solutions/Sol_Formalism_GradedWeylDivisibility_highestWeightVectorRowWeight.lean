-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.highestWeightVectorRowWeight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:20.660303+00:00
-- url     : https://prove2.me/submissions/c3ff5c4f-8471-4ef6-9e37-1b88fa70e976

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRowWeight
import Theorems.Thm_Formalism_GradedWeylDivisibility_extNu_anti
import Theorems.Thm_Formalism_GradedWeylDivisibility_sum_range_tsub_from
import Theorems.Thm_Formalism_GradedWeylDivisibility_lpMinor_rowHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GradedWeylDivisibility
open MvPolynomial
private theorem pow_nsmul' {σ M S : Type*} [CommSemiring S] [AddCommMonoid M]
    {w : σ → M} {φ : MvPolynomial σ S} {m : M} (hφ : IsWeightedHomogeneous w φ m) :
    ∀ k : ℕ, IsWeightedHomogeneous w (φ ^ k) (k • m) := by
  intro k
  induction k with
  | zero =>
    classical
    rw [pow_zero, zero_smul]
    intro d hd
    have hd0 : d = 0 := by
      by_contra h
      exact hd (by rw [MvPolynomial.coeff_one, if_neg (Ne.symm h)])
    rw [hd0, map_zero]
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul hφ
end Formalism.GradedWeylDivisibility
end

set_option autoImplicit false
open Formalism Formalism.GradedWeylDivisibility
open MvPolynomial
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : HWRowWeight := by
  intro R inst r n hn ν hν
  have hg : ∀ i j, i ≤ j → hwrowExtNu ν j ≤ hwrowExtNu ν i :=
    fun i j hij => extNu_anti hν hij
  have key : (rowNu (r := r) ν) =
      ∑ s : Fin n, (ν s - nuNext ν s) • (fun b : Fin r => if b.val < s.val + 1 then (1 : ℕ) else 0) := by
    funext a
    have hterm : ∀ s : Fin n, (ν s - nuNext ν s) * (if a.val < s.val + 1 then (1 : ℕ) else 0) =
        (fun i : ℕ => if a.val ≤ i then hwrowExtNu ν i - hwrowExtNu ν (i + 1) else 0) s.val := by
      intro s
      have hs : hwrowExtNu ν s.val = ν s := by
        first
        | simp [hwrowExtNu, s.isLt]
        | (unfold hwrowExtNu; rw [dif_pos s.isLt])
      have hs' : nuNext ν s = hwrowExtNu ν (s.val + 1) := rfl
      rw [hs', ← hs]
      by_cases h : a.val ≤ s.val
      · have h' : a.val < s.val + 1 := by omega
        simp [h, h']
      · have h' : ¬ a.val < s.val + 1 := by omega
        simp [h, h']
    have hsum : (∑ s : Fin n, (ν s - nuNext ν s) •
        (fun b : Fin r => if b.val < s.val + 1 then (1 : ℕ) else 0)) a =
        if a.val < n then hwrowExtNu ν a.val - hwrowExtNu ν n else 0 := by
      first
      | rw [Finset.sum_apply]
      | simp only [Finset.sum_apply]
      refine Eq.trans ?_ ((Fin.sum_univ_eq_sum_range
        (fun i : ℕ => if a.val ≤ i then hwrowExtNu ν i - hwrowExtNu ν (i + 1) else 0) n).trans
        (sum_range_tsub_from (hwrowExtNu ν) hg a.val n))
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      exact hterm s
    refine Eq.trans ?_ hsum.symm
    by_cases ha : a.val < n
    · have h0 : hwrowExtNu ν n = 0 := by
        first
        | simp [hwrowExtNu]
        | (unfold hwrowExtNu; rw [dif_neg (lt_irrefl n)])
      rw [if_pos ha, h0, Nat.sub_zero]
      all_goals first | rfl | simp [rowNu, hwrowExtNu, ha]
    · rw [if_neg ha]
      simp [rowNu, ha]
  rw [key]
  unfold hw
  apply IsWeightedHomogeneous.prod
  intro s _
  exact pow_nsmul'
    (lpMinor_rowHom R (s.val + 1)
      (Nat.succ_le_of_lt (lt_of_lt_of_le s.isLt hn)) (Nat.succ_le_of_lt s.isLt)) _
end Formalism.GradedWeylDivisibility
