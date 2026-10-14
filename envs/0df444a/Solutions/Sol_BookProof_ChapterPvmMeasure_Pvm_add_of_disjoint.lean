-- Prove2me | solution 1 for BookProof.ChapterPvmMeasure.Pvm.add_of_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T09:59:49.522609+00:00
-- url     : https://prove2.me/submissions/9fbdb028-d23c-4154-8c68-ab2d22b96b0e

-- Generated from ChapterPvmMeasure.lean — solution of BookProof.ChapterPvmMeasure.Pvm.add_of_disjoint
import Mathlib
import Definitions.Def_ChapterPvmMeasure
open BookProof.ChapterPvmMeasure
open BookProof.ChapterPvmMeasure.Pvm



open MeasureTheory
open scoped InnerProductSpace


variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (P : Pvm X H)

set_option maxHeartbeats 1000000 in
theorem solution {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hd : Disjoint E F) (u : H) : P.p (E ∪ F) u = P.p E u + P.p F u := by

  classical
  have hmeas : ∀ i : ℕ, MeasurableSet (if i = 0 then E else if i = 1 then F else (∅ : Set X)) := by
    intro i
    by_cases h0 : i = 0
    · simp [h0, hE]
    · by_cases h1 : i = 1 <;> simp [h0, h1, hF]
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun i : ℕ => if i = 0 then E else if i = 1 then F else (∅ : Set X))) := by
    intro i j hij
    simp only [Function.onFun]
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> by_cases hj0 : j = 0 <;>
      by_cases hj1 : j = 1 <;>
      simp_all [hd.symm]
  have hunion : (⋃ i : ℕ, if i = 0 then E else if i = 1 then F else (∅ : Set X)) = E ∪ F := by
    apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun i => ?_
      by_cases h0 : i = 0
      · simp [h0]
      · by_cases h1 : i = 1 <;> simp [h0, h1]
    · refine Set.union_subset ?_ ?_
      · intro x hx; exact Set.mem_iUnion.mpr ⟨0, by simpa using hx⟩
      · intro x hx; exact Set.mem_iUnion.mpr ⟨1, by simpa using hx⟩
  have hsum := P.hasSum _ hmeas hdisj u
  rw [hunion] at hsum
  have hsum2 : HasSum
      (fun i : ℕ => P.p (if i = 0 then E else if i = 1 then F else (∅ : Set X)) u)
      (∑ i ∈ ({0, 1} : Finset ℕ),
        P.p (if i = 0 then E else if i = 1 then F else (∅ : Set X)) u) := by
    refine hasSum_sum_of_ne_finset_zero ?_
    intro i hi
    have h0 : i ≠ 0 := fun h => hi (by simp [h])
    have h1 : i ≠ 1 := fun h => hi (by simp [h])
    simp [h0, h1, P.p_empty]
  have hval := hsum.unique hsum2
  rw [hval]
  simp
