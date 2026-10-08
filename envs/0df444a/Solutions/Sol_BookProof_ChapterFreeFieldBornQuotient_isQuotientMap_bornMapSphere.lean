-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornQuotient.isQuotientMap_bornMapSphere
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:27:56.875235+00:00
-- url     : https://prove2.me/submissions/f6d792be-4db8-476e-86aa-541ff656b75b

-- Quotient map proof using locally restated continuity and surjectivity.
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

private theorem local_surjective : Function.Surjective (bornMapSphere n) := by
  intro p
  refine ⟨⟨bornSection (p : Fin n → ℝ), sphere_section p⟩, ?_⟩
  apply Subtype.ext
  funext k
  change (Real.sqrt (p k)) ^ 2 = p k
  exact Real.sq_sqrt (p.property.1 k)



private theorem local_continuous : Continuous (bornMapSphere n) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro k
  exact ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) k).comp continuous_subtype_val).pow 2

theorem solution : Topology.IsQuotientMap (bornMapSphere n) := by
  letI : CompactSpace ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  exact local_continuous.isClosedMap.isQuotientMap local_continuous local_surjective

#print axioms solution
