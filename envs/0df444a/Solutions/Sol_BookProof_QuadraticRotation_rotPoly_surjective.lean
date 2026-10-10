-- Prove2me | solution 1 for BookProof.QuadraticRotation.rotPoly_surjective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T14:43:47.860168+00:00
-- url     : https://prove2.me/submissions/dc2b0e86-69bc-4aa4-8c1c-f23f228a335f

import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
open BookProof.QuadraticRotation

open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

theorem solution {d : ℕ} {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) :
    Function.Surjective (rotPoly O) := by
  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  have key : (rotPoly O).comp (rotPoly Oᵀ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, AlgHom.id_apply, rotPoly, aeval_X, map_sum, map_mul,
      algHom_C, transpose_apply]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ k : Fin d, (∑ j, (algebraMap ℂ (MvPolynomial (Fin d) ℂ)) ((O i j : ℝ) : ℂ) *
        (C ((O k j : ℝ) : ℂ) * X k)) = C (((O * Oᵀ) i k : ℝ) : ℂ) * X k := by
      intro k
      rw [Matrix.mul_apply]
      simp only [transpose_apply, algebraMap_eq, ← mul_assoc, ← map_mul, ← Finset.sum_mul,
        ← map_sum]
      push_cast
      rfl
    simp only [this, hOO, one_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  intro p
  refine ⟨rotPoly Oᵀ p, ?_⟩
  have := congrArg (fun f => f p) key
  simpa using this
