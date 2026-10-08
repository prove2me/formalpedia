-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornQuotient.surjective_bornMapSphere
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:27:55.832785+00:00
-- url     : https://prove2.me/submissions/3c79a8b6-c5c5-4600-a928-80d1e0f83b46

-- Generated from ChapterFreeFieldBornQuotient.lean — theorem BookProof.ChapterFreeFieldBornQuotient.surjective_bornMapSphere
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Mathlib
import Definitions.Def_ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornQuotient

variable {n : ℕ}


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont

private theorem sphere_section (p : ↥(stdSimplex ℝ (Fin n))) :
    bornSection (p : Fin n → ℝ) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  have hsq : ‖bornSection (p : Fin n → ℝ)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ k : Fin n, ‖Real.sqrt (p k)‖ ^ 2) = 1
    simp only [Real.norm_eq_abs, sq_abs]
    calc
      (∑ k : Fin n, Real.sqrt (p k) ^ 2) = ∑ k : Fin n, p k :=
        Finset.sum_congr rfl (fun k _ => Real.sq_sqrt (p.property.1 k))
      _ = 1 := p.property.2
  have hn : ‖bornSection (p : Fin n → ℝ)‖ = 1 := by
    nlinarith [norm_nonneg (bornSection (p : Fin n → ℝ))]
  simpa using hn

theorem solution : Function.Surjective (bornMapSphere n) := by
  intro p
  refine ⟨⟨bornSection (p : Fin n → ℝ), sphere_section p⟩, ?_⟩
  apply Subtype.ext
  funext k
  change (Real.sqrt (p k)) ^ 2 = p k
  exact Real.sq_sqrt (p.property.1 k)

#print axioms solution
