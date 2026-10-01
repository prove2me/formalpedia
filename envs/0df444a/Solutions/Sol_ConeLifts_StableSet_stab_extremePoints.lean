-- Prove2me | solution 1 for ConeLifts.StableSet.stab_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:24:10.466755+00:00
-- url     : https://prove2.me/submissions/f4c54602-73c1-4892-a4be-150856bb9276

import Definitions.Def_ConeLifts_StableSet_stab
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic
open Set
open ConeLifts.StableSet

private lemma coordinates {n : ℕ} (G : SimpleGraph (Fin n)) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ stab G) : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  apply convexHull_min (t := {x : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ x i ∧ x i ≤ 1}) ?_ ?_ hx
  · rintro x ⟨S, hS, rfl⟩ i
    change 0 ≤ (if i ∈ S then (1:ℝ) else 0) ∧ (if i ∈ S then (1:ℝ) else 0) ≤ 1
    split_ifs <;> norm_num
  · intro x hx y hy a b ha hb hab i
    change 0 ≤ a * x i + b * y i ∧ a * x i + b * y i ≤ 1
    constructor
    · exact add_nonneg (mul_nonneg ha (hx i).1) (mul_nonneg hb (hy i).1)
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr (hx i).2),
        mul_nonneg hb (sub_nonneg.mpr (hy i).2)]

private lemma vertex {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : G.IsIndepSet (S : Set (Fin n))) :
    incidenceVector S ∈ Set.extremePoints ℝ (stab G) := by
  classical
  refine ⟨subset_convexHull ℝ _ ⟨S, hS, rfl⟩, ?_⟩
  intro x hx y hy hz
  rcases hz with ⟨a, b, ha, hb, hab, heq⟩
  ext i
  have hi := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z i) heq
  change a * x i + b * y i = (if i ∈ S then 1 else 0) at hi
  change x i = (if i ∈ S then 1 else 0)
  have hx := coordinates G hx i
  have hy := coordinates G hy i
  split_ifs at hi ⊢ with h
  · nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hy.2)]
  · nlinarith [mul_nonneg hb.le hy.1]

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ Set.extremePoints ℝ (stab G) ∧
      ∀ i : Fin n, EuclideanSpace.single i (1 : ℝ) ∈ Set.extremePoints ℝ (stab G) := by
  classical
  constructor
  · convert vertex G ∅ (by simp [SimpleGraph.isIndepSet_iff]) using 1
    ext i
    simp [incidenceVector]
  · intro i
    convert vertex G {i} (by simp [SimpleGraph.isIndepSet_iff]) using 1
    ext j
    simp [incidenceVector, EuclideanSpace.single_apply, eq_comm]
