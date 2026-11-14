-- Prove2me | solution 1 for ConsistentSubmodular.CompatibleProfile.checkpoint_of_finite_checkpoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:11.924386+00:00
-- url     : https://prove2.me/submissions/7bb675bf-f983-44d6-894e-f78b2f55b8c4

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_CompletionReduction
import Theorems.Thm_ConsistentSubmodular_sum_weight_disjoint
import Theorems.Thm_ConsistentSubmodular_TriangularArray_atomic_residual
import Theorems.Thm_ConsistentSubmodular_CompatibleProfile_triangular_baseline_le

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteExpectation_add (p : ι → ℝ) (v w : Finset ι → ℝ) :
    finiteExpectation p (fun S => v S + w S) = finiteExpectation p v + finiteExpectation p w := by
  simp only [finiteExpectation, mul_add, Finset.sum_add_distrib]

theorem finiteExpectation_mul (p : ι → ℝ) (c : ℝ) (v : Finset ι → ℝ) :
    finiteExpectation p (fun S => c * v S) = c * finiteExpectation p v := by
  simp only [finiteExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem finiteExpectation_sum {β : Type*} [Fintype β] (p : ι → ℝ)
    (v : β → Finset ι → ℝ) :
    finiteExpectation p (fun S => ∑ a, v a S) = ∑ a, finiteExpectation p (v a) := by
  simp only [finiteExpectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem finiteExpectation_hit (p : ι → ℝ) (L : Finset ι) :
    finiteExpectation p (fun S => if (L ∩ S).Nonempty then 1 else 0) =
      1 - ∏ i ∈ L, (1 - p i) := by
  have hterm (S : Finset ι) : bernoulliWeight p S * (if (L ∩ S).Nonempty then 1 else 0) =
      bernoulliWeight p S - (if Disjoint S L then bernoulliWeight p S else 0) := by
    have hiff : (L ∩ S).Nonempty ↔ ¬Disjoint S L := by
      rw [Finset.inter_comm, Finset.not_disjoint_iff_nonempty_inter]
    by_cases hd : Disjoint S L <;> simp [hiff, hd]
  unfold finiteExpectation
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, sum_bernoulliWeight, sum_weight_disjoint]

theorem finiteExpectation_weighted_hit (p : ι → ℝ) (L : Finset ι) (w : ℝ) :
    finiteExpectation p (fun S => if (L ∩ S).Nonempty then w else 0) =
      w * (1 - ∏ i ∈ L, (1 - p i)) := by
  have hpoint : (fun S => if (L ∩ S).Nonempty then w else 0) =
      (fun S => w * (if (L ∩ S).Nonempty then 1 else 0)) := by
    funext S
    split_ifs <;> simp
  rw [hpoint, finiteExpectation_mul, finiteExpectation_hit]

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace CompatibleProfile

variable {d : ℕ} (P : CompatibleProfile d)

theorem poolValue_le_residual_drop (t : ℕ) (I : Finset (Fin d)) :
    P.poolValue t I ≤ P.residualOn t I - P.residualOn (t + 1) I := by
  apply finiteMaximum_le
  · exact sub_nonneg.mpr (P.residualOn_antitone (Nat.le_succ t) I)
  · intro i hi
    have h := P.marginals_decrease t (t + 1) (Nat.le_succ t) {i} I
      (Finset.singleton_subset_iff.mpr hi)
    dsimp [loss, residual, residualOn, baseline]
    linarith

theorem terminalValue_le_residual (m : ℕ) (I : Finset (Fin d)) :
    P.terminalValue m I ≤ P.residualOn m I := by
  apply finiteMaximum_le (P.residualOn_nonnegative m I)
  intro i hi
  exact sub_le_sub_right ((P.objective m).monotone {i} I
    (Finset.singleton_subset_iff.mpr hi)) _

end CompatibleProfile

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {m atomCount : ℕ}

namespace AtomicProfile

variable (P : AtomicProfile m atomCount)

/-- The atomic polynomial is exactly its finite independent type expectation. -/
theorem value_eq_expectation (t : Fin (m + 1)) (p : Point m) :
    P.value t p = finiteExpectation p (P.unionValue t) := by
  unfold unionValue
  rw [finiteExpectation_add, finiteExpectation_const, finiteExpectation_sum]
  unfold value
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : t ≤ P.pool a
  · simp only [ha, true_and, ite_true]
    exact (finiteExpectation_weighted_hit p (P.labels a) (P.weight a)).symm
  · simp only [ha, false_and, ite_false, finiteExpectation_const]

end AtomicProfile

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace TriangularArray

variable {m : ℕ} (M : TriangularArray m)

theorem toAtomic_canonical : M.toAtomic.Canonical := by
  constructor
  · unfold AtomicProfile.designated
    rw [M.atomic_residual]
    simpa using M.initial
  · intro t i
    unfold AtomicProfile.designated
    rw [M.atomic_residual, M.atomic_residual]
    exact M.dominated i t

theorem coverage_total (j : Fin (m + 1)) :
    (∑ a, (M.coverage j).weight a) = finiteMaximum Finset.univ (fun i => M.length i j) := by
  have h := (M.coverage j).value_eq Finset.univ
  simpa [(M.coverage j).labels_nonempty] using h.symm

theorem atomic_baseline (t : Fin (m + 1)) :
    M.toAtomic.baseline t =
      ∑ j, if j < t then finiteMaximum Finset.univ (fun i => M.length i j) else 0 := by
  change (∑ a, if (M.atomEquiv.symm a).1 < t then
    (M.coverage (M.atomEquiv.symm a).1).weight (M.atomEquiv.symm a).2 else 0) = _
  rw [M.atomEquiv.symm.sum_comp (fun a : M.AtomIndex =>
    if a.1 < t then (M.coverage a.1).weight a.2 else 0), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < t
  · simpa only [hj, ite_true] using M.coverage_total j
  · simp [hj]

theorem atomic_unionValue (t : Fin (m + 1)) (I : Finset (Fin (m + 1))) :
    (∑ a, if t ≤ M.toAtomic.pool a ∧ (M.toAtomic.labels a ∩ I).Nonempty
      then M.toAtomic.weight a else 0) =
      ∑ j, if t ≤ j then finiteMaximum I (fun i => M.length i j) else 0 := by
  change (∑ a, if t ≤ (M.atomEquiv.symm a).1 ∧
      ((M.coverage (M.atomEquiv.symm a).1).labels (M.atomEquiv.symm a).2 ∩ I).Nonempty
    then (M.coverage (M.atomEquiv.symm a).1).weight (M.atomEquiv.symm a).2 else 0) = _
  rw [M.atomEquiv.symm.sum_comp (fun a : M.AtomIndex =>
    if t ≤ a.1 ∧ ((M.coverage a.1).labels a.2 ∩ I).Nonempty then (M.coverage a.1).weight a.2 else 0), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : t ≤ j
  · simpa only [hj, true_and, ite_true] using ((M.coverage j).value_eq I).symm
  · simp [hj]

end TriangularArray

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

theorem fin_tail_last {m : ℕ} (a : Fin (m + 1) → ℝ) :
    (∑ j, if Fin.last m ≤ j then a j else 0) = a (Fin.last m) := by
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro j _ hj
    have hn : ¬Fin.last m ≤ j := fun h => hj (le_antisymm (Fin.le_last j) h)
    simp [hn]
  · simp

namespace CompatibleProfile

variable {m : ℕ} (P : CompatibleProfile (m + 1))

theorem triangular_pool_le_raw (I : Finset (Fin (m + 1))) (j : Fin (m + 1)) :
    finiteMaximum I (fun i => P.triangularLength i j) ≤
      finiteMaximum I (fun i => P.rawLength i j) := by
  apply finiteMaximum_le (finiteMaximum_nonnegative (fun i _ => P.rawLength_nonnegative i j))
  exact fun i hi => (P.triangularLength_le_raw i j).trans
    (le_finiteMaximum (g := fun i => P.rawLength i j) hi)

theorem raw_union_tail_le (I : Finset (Fin (m + 1))) (t : Fin (m + 1)) :
    (∑ j, if t ≤ j then finiteMaximum I (fun i => P.rawLength i j) else 0) ≤
      P.residualOn t.val I := by
  induction t using Fin.reverseInduction with
  | last =>
    rw [fin_tail_last]
    simpa only [rawLength, terminalValue, ite_true, Fin.val_last] using P.terminalValue_le_residual m I
  | cast t ih =>
    rw [fin_tail_step]
    have hpool := P.poolValue_le_residual_drop t.val I
    have hraw : finiteMaximum I (fun i => P.rawLength i t.castSucc) = P.poolValue t.val I := by
      simp only [rawLength, Fin.castSucc_ne_last, ite_false, Fin.val_castSucc, poolValue]
    rw [hraw]
    simp only [Fin.val_succ, Fin.val_castSucc] at *
    linarith

theorem triangular_union_tail_le (I : Finset (Fin (m + 1))) (t : Fin (m + 1)) :
    (∑ j, if t ≤ j then finiteMaximum I (fun i => P.triangularLength i j) else 0) ≤
      P.residualOn t.val I := by
  apply le_trans _ (P.raw_union_tail_le I t)
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact P.triangular_pool_le_raw I j
  · rfl

end CompatibleProfile

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace CompatibleProfile

variable {m : ℕ} (P : CompatibleProfile (m + 1))

variable (hinit : P.residual 0 0 = 1)

variable (hopt : ∀ t : Fin (m + 1), ∀ i, P.residual t.val i ≤ P.residual t.val t)

theorem atomicCompletion_canonical : (P.atomicCompletion hinit hopt).Canonical :=
  (P.toTriangularArray hinit hopt).toAtomic_canonical

theorem atomicCompletion_designated (t : Fin (m + 1)) :
    (P.atomicCompletion hinit hopt).designated t = P.residual t.val t := by
  unfold atomicCompletion AtomicProfile.designated
  rw [TriangularArray.atomic_residual]
  exact P.triangularLength_designated t

theorem atomicCompletion_baseline_le (t : Fin (m + 1)) :
    (P.atomicCompletion hinit hopt).baseline t ≤ P.baseline t.val := by
  unfold atomicCompletion
  rw [TriangularArray.atomic_baseline]
  exact P.triangular_baseline_le t

/-- Adding back the exact baseline slack gives pointwise Boolean domination. -/
theorem atomicCompletion_unionValue_le (t : Fin (m + 1)) (I : Finset (Fin (m + 1))) :
    (P.atomicCompletion hinit hopt).unionValue t I +
      (P.baseline t.val - (P.atomicCompletion hinit hopt).baseline t) ≤
      (P.objective t.val).value I := by
  have hres := P.triangular_union_tail_le I t
  unfold AtomicProfile.unionValue atomicCompletion
  rw [TriangularArray.atomic_unionValue]
  change (P.toTriangularArray hinit hopt).toAtomic.baseline t +
      (∑ j, if t ≤ j then finiteMaximum I (fun i => P.triangularLength i j) else 0) +
      (P.baseline t.val - (P.toTriangularArray hinit hopt).toAtomic.baseline t) ≤ _
  dsimp [residualOn] at hres
  linarith

/-- Finite expectation preserves the completion inequality on the entire cube. -/
theorem atomicCompletion_multilinear_le (t : Fin (m + 1)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    (P.atomicCompletion hinit hopt).value t p +
      (P.baseline t.val - (P.atomicCompletion hinit hopt).baseline t) ≤
      P.multilinearValue t.val p := by
  have h := finiteExpectation_mono p hp (P.atomicCompletion_unionValue_le hinit hopt t)
  rw [finiteExpectation_add, finiteExpectation_const,
    ← AtomicProfile.value_eq_expectation] at h
  exact h

/-- Baseline restoration incurs no additional approximation factor. -/
theorem atomicCompletion_approximation_transfer (t : Fin (m + 1)) (p : Point m)
    (hp : IsSimplex p) {α : ℝ} (hα : α ≤ 1)
    (hgood : α * (P.atomicCompletion hinit hopt).benchmark t ≤
      (P.atomicCompletion hinit hopt).value t p) :
    α * (P.objective t.val).value {t} ≤ P.multilinearValue t.val p := by
  have hdom := P.atomicCompletion_multilinear_le hinit hopt t p
    (fun i => ⟨hp.1 i, hp.coordinate_le_one i⟩)
  have hbase := P.atomicCompletion_baseline_le hinit hopt t
  have hmul := mul_le_of_le_one_left (sub_nonneg.mpr hbase) hα
  unfold AtomicProfile.benchmark at hgood
  rw [P.atomicCompletion_designated hinit hopt t] at hgood
  dsimp [residual, residualOn] at hgood
  nlinarith

theorem atomicCompletion_path_transfer (t : Fin (m + 1)) (γ : PolygonalPath m)
    {α : ℝ} (hα : α ≤ 1)
    (hγ : ConsistentSubmodular.SafePath (P.atomicCompletion hinit hopt) t
      (α * (P.atomicCompletion hinit hopt).benchmark t) γ) :
    P.SafePath t.val (α * (P.objective t.val).value {t}) γ := by
  constructor
  · intro j
    exact ⟨(hγ.1 j).1, P.atomicCompletion_approximation_transfer hinit hopt t _ (hγ.1 j).1 hα (hγ.1 j).2⟩
  · intro j x hx hx'
    have h := hγ.2 j x hx hx'
    exact ⟨h.1, P.atomicCompletion_approximation_transfer hinit hopt t _ h.1 hα h.2⟩

end CompatibleProfile

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.CompatibleProfile
variable {m : ℕ} (P : CompatibleProfile (m + 1))
variable (hinit : P.residual 0 0 = 1)
variable (hopt : ∀ t : Fin (m + 1), ∀ i, P.residual t.val i ≤ P.residual t.val t)

include hinit hopt in
theorem solution (hfinite : FiniteCheckpointGoal) :
    ∃ (p : Point m) (entry exit : PolygonalPath m),
      IsSimplex p ∧ supportCard p ≤ 2 ∧
      (∀ t : Fin (m + 1), (3 : ℝ) / 4 * (P.objective t.val).value {t} ≤ P.multilinearValue t.val p) ∧
      entry.node 0 = vertex 0 ∧
      entry.node (Fin.last entry.pieces) = p ∧
      exit.node 0 = p ∧
      exit.node (Fin.last exit.pieces) = vertex (Fin.last m) ∧
      P.SafePath 0 ((3 : ℝ) / 4 * (P.objective 0).value {0}) entry ∧
      P.SafePath m ((3 : ℝ) / 4 * (P.objective m).value {Fin.last m}) exit ∧
      entry.pieces + exit.pieces ≤ (m + 1) + 2 := by
  obtain ⟨p, entry, exit, hp, hsupport, hstage, he0, he1, hx0, hx1, hentry, hexit, hpieces⟩ :=
    hfinite m _ (P.atomicCompletion hinit hopt) (P.atomicCompletion_canonical hinit hopt)
  have hbenchmark0 : (P.atomicCompletion hinit hopt).benchmark 0 = 1 := by
    unfold AtomicProfile.benchmark
    rw [P.atomicCompletion_designated hinit hopt]
    simp [AtomicProfile.baseline, hinit]
  refine ⟨p, entry, exit, hp, hsupport, ?_, he0, he1, hx0, hx1, ?_, ?_, hpieces⟩
  · intro t
    exact P.atomicCompletion_approximation_transfer hinit hopt t p hp (by norm_num) (hstage t)
  · apply P.atomicCompletion_path_transfer hinit hopt 0 entry (by norm_num : (3 : ℝ) / 4 ≤ 1)
    simpa only [hbenchmark0, mul_one] using hentry
  · exact P.atomicCompletion_path_transfer hinit hopt (Fin.last m) exit (by norm_num) hexit

end
