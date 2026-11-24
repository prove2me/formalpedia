-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.psi_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.572824+00:00
-- url     : https://prove2.me/submissions/70cc1f84-e9a8-4e36-8742-6074493fd794

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_idx_empty
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_idxWeight_eq

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open A3comb
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : PsiWeight := by
  intro R _ n N isVec B μ I hp hI
  have hmon : ∀ (d : ℕ × Fin n →₀ ℕ) (r : R), IsWeightedHomogeneous (torusW isVec)
      (MvPolynomial.monomial d r) (Finsupp.weight (torusW isVec) d) :=
    fun d r => MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl
  have hXw : ∀ x : ℕ × Fin n, IsWeightedHomogeneous (torusW isVec)
      (X x : MvPolynomial (ℕ × Fin n) R) (torusW isVec x) := by
    intro x
    have := hmon (Finsupp.single x 1) 1
    simp only [Finsupp.weight_apply, Finsupp.sum_single_index, zero_smul, one_smul] at this
    exact this
  have wedgeW : ∀ (c : ℤ) (k : ℕ) (J : Finset (Fin n)) (m : Fin n), m ∈ J →
      (isVec k == decide (1 ≤ c)) = true →
      (fun a => if a ∈ J then (if 1 ≤ c then (1 : ℤ) else -1) else 0) =
        (fun a => if a ∈ J.erase m then (if 1 ≤ c then (1 : ℤ) else -1) else 0) +
          torusW isVec (k, m) := by
    intro c k J m hm hup
    funext a
    simp only [Pi.add_apply, torusW, ite_apply, Finset.mem_erase, Pi.single_apply, Pi.neg_apply]
    by_cases hc : 1 ≤ c
    · simp only [if_pos hc, decide_eq_true hc] at hup ⊢
      by_cases hv : isVec k = true <;> by_cases ha : a = m <;> simp_all
    · simp only [if_neg hc, decide_eq_false hc] at hup ⊢
      by_cases hv : isVec k = true <;> by_cases ha : a = m <;> simp_all
  have contrW : ∀ (c : ℤ) (k : ℕ) (J : Finset (Fin n)) (m : Fin n), m ∉ J →
      ¬ (isVec k == decide (1 ≤ c)) = true →
      (fun a => if a ∈ J then (if 1 ≤ c then (1 : ℤ) else -1) else 0) =
        torusW isVec (k, m) +
          (fun a => if a ∈ insert m J then (if 1 ≤ c then (1 : ℤ) else -1) else 0) := by
    intro c k J m hm hup
    funext a
    simp only [Pi.add_apply, torusW, ite_apply, Finset.mem_insert, Pi.single_apply, Pi.neg_apply]
    by_cases hc : 1 ≤ c
    · simp only [if_pos hc, decide_eq_true hc] at hup ⊢
      by_cases hv : isVec k = true <;> by_cases ha : a = m <;> simp_all
    · simp only [if_neg hc, decide_eq_false hc] at hup ⊢
      by_cases hv : isVec k = true <;> by_cases ha : a = m <;> simp_all
  have key : ∀ c : ℤ, ∀ k : ℕ, ∀ J : Finset (Fin n),
      IsWeightedHomogeneous (torusW isVec)
        (pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) k J)
        (fun a => if a ∈ J then (if 1 ≤ c then (1 : ℤ) else -1) else 0) := by
    intro c k
    induction k with
    | zero =>
      intro J
      simp only [pathWord, oneF]
      by_cases hJ : J = ∅
      · subst hJ
        rw [if_pos rfl]
        have h0 : (fun a : Fin n => if a ∈ (∅ : Finset (Fin n)) then
            (if 1 ≤ c then (1 : ℤ) else -1) else 0) = 0 := by
          funext a
          simp
        rw [h0]
        have := hmon 0 1
        rw [map_zero] at this
        exact this
      · rw [if_neg hJ]
        exact (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.zero_mem _)
    | succ k ih =>
      intro J
      simp only [pathWord]
      by_cases hcol : colHeight (μ (k + 1)) c = colHeight (μ k) c
      · rw [if_pos hcol]
        exact ih J
      · rw [if_neg hcol]
        unfold stepF
        by_cases hup : (isVec k == decide (1 ≤ c)) = true
        · rw [if_pos hup]
          unfold wedgeF
          beta_reduce
          apply (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp
          refine Submodule.sum_mem _ fun m hm => ?_
          rw [mul_assoc, ← zsmul_eq_mul]
          refine zsmul_mem ?_ _
          apply (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
          rw [wedgeW c k J m hm hup]
          exact (ih (J.erase m)).mul (hXw (k, m))
        · rw [if_neg hup]
          unfold contrF
          beta_reduce
          apply (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp
          refine Submodule.sum_mem _ fun m hm => ?_
          rw [mul_assoc, ← zsmul_eq_mul]
          refine zsmul_mem ?_ _
          apply (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
          rw [contrW c k J m (Finset.mem_compl.mp hm) hup]
          exact (hXw (k, m)).mul (ih (insert m J))
  obtain ⟨T, hb⟩ : ∃ T : ℤ, ∀ k ≤ N, ∀ m, |μ k m| ≤ T := by
    refine ⟨∑ k ∈ range (N + 1), ∑ m, |μ k m|, fun k hk m => ?_⟩
    calc |μ k m| ≤ ∑ m', |μ k m'| :=
          Finset.single_le_sum (f := fun m' => |μ k m'|) (fun i _ => abs_nonneg _)
            (Finset.mem_univ m)
      _ ≤ ∑ k' ∈ range (N + 1), ∑ m', |μ k' m'| :=
          Finset.single_le_sum (f := fun k' => ∑ m', |μ k' m'|)
            (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
            (Finset.mem_range.mpr (by omega))
  have hS : ∀ c, c ∉ Finset.Icc (-T) T → I c = ∅ := fun c hc => idx_empty hI T (hb N le_rfl) c hc
  have hone : ∀ c, c ∉ Finset.Icc (-T) T → ∀ k ≤ N,
      pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) k = oneF := by
    intro c hc k
    induction k with
    | zero =>
      intro _
      simp only [pathWord]
    | succ k ih =>
      intro hk
      rw [Finset.mem_Icc] at hc
      have hcol : colHeight (μ (k + 1)) c = colHeight (μ k) c := by
        by_cases hcT : T < c
        · have e : ∀ k' ≤ N, colHeight (μ k') c = 0 := by
            intro k' hk'
            unfold colHeight
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro m _
            have := hb k' hk' m
            rw [abs_le] at this
            omega
          rw [e (k + 1) hk, e k (by omega)]
        · have e : ∀ k' ≤ N, colHeight (μ k') c = n := by
            intro k' hk'
            unfold colHeight
            rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
            intro m _
            have := hb k' hk' m
            rw [abs_le] at this
            omega
          rw [e (k + 1) hk, e k (by omega)]
      simp only [pathWord]
      rw [if_pos hcol]
      exact ih (by omega)
  have hsupp : Function.mulSupport (fun c => pathWord isVec μ c
      (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c)) ⊆ ↑(Finset.Icc (-T) T) := by
    intro c hc
    rw [Function.mem_mulSupport] at hc
    by_contra hcS
    apply hc
    rw [hone c hcS N le_rfl, hS c hcS]
    simp [oneF]
  unfold psiPath
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod (Finset.Icc (-T) T) _ _
    (fun c _ => key c N (I c))
  convert hprod using 1
  funext a
  rw [Finset.sum_apply, idxWeight_eq I (Finset.Icc (-T) T) hS a]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
