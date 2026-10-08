-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.shiftCol_opCol
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:30:05.142999+00:00
-- url     : https://prove2.me/submissions/9c66deda-02fe-4f5f-b609-f33a016bb7c9

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.shiftCol_opCol
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.FockNumberPreservingGap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

private theorem coordinate_spec (b : HilbertBasis ℕ ℂ F)
    (x : F) (hx : x ∈ finiteModeDomain b) :
    Finsupp.linearCombination ℂ b (coordFinsupp b x) = x := by
  classical
  simp only [coordFinsupp, dif_pos hx]
  exact (Finsupp.mem_span_range_iff_exists_finsupp.mp hx).choose_spec

theorem solution (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) (mu : ℝ) :
    shiftCol (opCol b A) mu = opCol b (A - ((mu : ℝ) : ℂ) • LinearMap.id) := by
  classical
  funext k
  let v : finiteModeDomain b := ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩
  let B : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b := A - (mu : ℂ) • LinearMap.id
  apply b.orthonormal.linearIndependent.finsuppLinearCombination_injective
  change Finsupp.linearCombination ℂ b
      (coordFinsupp b (A v : F) -
        (mu : ℂ) • Finsupp.single k 1) =
    Finsupp.linearCombination ℂ b (coordFinsupp b (B v : F))
  rw [map_sub, map_smul, Finsupp.linearCombination_single, one_smul,
    coordinate_spec b _ (A v).property, coordinate_spec b _ (B v).property]
  rfl

#print axioms solution
