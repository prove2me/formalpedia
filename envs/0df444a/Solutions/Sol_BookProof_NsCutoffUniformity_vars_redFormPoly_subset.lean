-- Prove2me | solution 1 for BookProof.NsCutoffUniformity.vars_redFormPoly_subset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T22:36:53.635366+00:00
-- url     : https://prove2.me/submissions/aead2ec7-66ed-48fc-8c64-d9841d48c10a

-- Generated from ChapterNsCutoffUniformity.lean — solution of BookProof.NsCutoffUniformity.vars_redFormPoly_subset
import Mathlib
import Definitions.Def_ChapterNsCutoffUniformity
import Definitions.Def_ChapterNavierStokesFullEulerianFock
open BookProof.NsCutoffUniformity




open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

variable {n : ℕ}
variable {ι : Type*}
variable (nu : ℝ) (k : Fin 3 → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (nu : ℝ) (k : Fin 3 → ℝ) (p : Fin n) (r : Fin 7) :
    (redFormPoly nu k n p r).vars ⊆ Finset.image (redIdx p) Finset.univ := by

  classical
  have hmemU : ∀ i : Fin 3, ruIdx p i ∈ Finset.image (redIdx p) (Finset.univ : Finset (Fin 6)) :=
    fun i => Finset.mem_image.2 ⟨ruIdx6 i, Finset.mem_univ _, rfl⟩
  have hmemQ : ∀ i : Fin 3, rqIdx p i ∈ Finset.image (redIdx p) (Finset.univ : Finset (Fin 6)) :=
    fun i => Finset.mem_image.2 ⟨rqIdx6 i, Finset.mem_univ _, rfl⟩
  have hX : ∀ a : Fin (n * 6), a ∈ Finset.image (redIdx p) (Finset.univ : Finset (Fin 6)) →
      (X a : MvPolynomial (Fin (n * 6)) ℂ).vars ⊆ Finset.image (redIdx p) Finset.univ := by
    intro a ha
    rw [vars_X]
    exact Finset.singleton_subset_iff.2 ha
  have hCX : ∀ (c : ℂ) (a : Fin (n * 6)),
      a ∈ Finset.image (redIdx p) (Finset.univ : Finset (Fin 6)) →
      (C c * X a : MvPolynomial (Fin (n * 6)) ℂ).vars
        ⊆ Finset.image (redIdx p) Finset.univ := by
    intro c a ha
    refine (vars_mul _ _).trans (Finset.union_subset ?_ (hX a ha))
    simp [vars_C]
  have hCXX : ∀ (c : ℂ) (a b : Fin (n * 6)),
      a ∈ Finset.image (redIdx p) (Finset.univ : Finset (Fin 6)) →
      b ∈ Finset.image (redIdx p) (Finset.univ : Finset (Fin 6)) →
      (C c * (X a * X b) : MvPolynomial (Fin (n * 6)) ℂ).vars
        ⊆ Finset.image (redIdx p) Finset.univ := by
    intro c a b ha hb
    refine (vars_mul _ _).trans (Finset.union_subset ?_ ?_)
    · simp [vars_C]
    · exact (vars_mul _ _).trans (Finset.union_subset (hX a ha) (hX b hb))
  rw [redFormPoly]
  split
  · exact (vars_add_subset _ _).trans
      (Finset.union_subset (hX _ (hmemQ _)) (hCX _ _ (hmemU _)))
  · split
    · refine (vars_sum_subset _ _).trans (Finset.biUnion_subset.2 fun j _ => ?_)
      exact hCXX _ _ _ (hmemU _) (hmemU _)
    · refine (vars_sum_subset _ _).trans (Finset.biUnion_subset.2 fun j _ => ?_)
      exact hCX _ _ (hmemU _)
