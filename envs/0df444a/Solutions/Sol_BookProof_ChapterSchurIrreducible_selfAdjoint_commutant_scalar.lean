-- Prove2me | solution 1 for BookProof.ChapterSchurIrreducible.selfAdjoint_commutant_scalar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:27:01.844157+00:00
-- url     : https://prove2.me/submissions/c85853c9-91f2-496d-9d02-91c55c5c867f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSchurIrreducible.lean — solution of BookProof.ChapterSchurIrreducible.selfAdjoint_commutant_scalar
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Theorems.Thm_BookProof_ChapterSchurIrreducible_spectrum_subsingleton_of_irreducible
import Definitions.Def_ChapterA
open BookProof.ChapterSchurIrreducible



open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System
open BookProof.ChapterA
open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (M : System ℂ V) (hirr : M.IsIrreducible)
    {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) (hcomm : M.Commutes T) :
    ∃ c : ℝ, T = (c : ℂ) • (1 : V →L[ℂ] V) := by

  by_cases hV : Nontrivial V
  · -- Pick the (unique) spectral value, or `0` if the spectrum is empty.
    classical
    by_cases hne : (spectrum ℝ T).Nonempty
    · obtain ⟨c, hc⟩ := hne
      refine ⟨c, ?_⟩
      have hall : ∀ x ∈ spectrum ℝ T, x = c := fun x hx =>
        spectrum_subsingleton_of_irreducible M hirr hT hcomm hx hc
      have h1 : cfc (fun x : ℝ => x) T = T := cfc_id ℝ T
      rw [← h1, cfc_congr (g := fun _ => c) (fun x hx => hall x hx), cfc_const c T]
      simp [Algebra.algebraMap_eq_smul_one]
    · refine ⟨0, ?_⟩
      have hall : ∀ x ∈ spectrum ℝ T, x = (0 : ℝ) := by
        intro x hx; exact absurd ⟨x, hx⟩ hne
      have h1 : cfc (fun x : ℝ => x) T = T := cfc_id ℝ T
      rw [← h1, cfc_congr (g := fun _ => (0 : ℝ)) (fun x hx => hall x hx), cfc_const (0 : ℝ) T]
      simp
  · refine ⟨0, ?_⟩
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    ext x
    exact Subsingleton.elim _ _
