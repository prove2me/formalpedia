-- Prove2me | solution 1 for BaconThesis.Control.eq_3_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:17:13.214378+00:00
-- url     : https://prove2.me/submissions/0c9f6399-1761-4d89-9c97-8bc9fa21d2e9

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_IsDensityOperator

open scoped Matrix

open scoped MatrixOrder ComplexOrder

theorem solution {a ι : Type} [Fintype a] [DecidableEq a] [Fintype ι]
    (ρ : ι → Matrix a a ℂ) (hρ : ∀ i, WildeQIT.IsDensityOperator (ρ i))
    (hcomm : ∀ i j, ρ i * ρ j = ρ j * ρ i) :
    ∃ v : ι → (a × (a × ι)) → ℂ,
      (∀ i, WildeQIT.partialTraceRight (Matrix.vecMulVec (v i) (star (v i))) = ρ i) ∧
      ∀ i j, i ≠ j → star (v i) ⬝ᵥ v j = 0 := by
  classical
  have hex : ∀ i, ∃ B : Matrix a a ℂ, ρ i = star B * B := fun i =>
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hρ i).1.nonneg
  choose B hB using hex
  refine ⟨fun i p => if p.2.2 = i then star (B i p.2.1 p.1) else 0, fun i => ?_, fun i j hij => ?_⟩
  · ext x x'
    simp only [WildeQIT.partialTraceRight, Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    rw [hB i, Matrix.mul_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.sum_eq_single i]
    · simp only [↓reduceIte, star_star, Matrix.star_apply]
    · intro k _ hk
      simp only [hk, ↓reduceIte, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  · unfold dotProduct
    refine Finset.sum_eq_zero (fun p _ => ?_)
    simp only [Pi.star_apply]
    by_cases h : p.2.2 = i
    · have : ¬ p.2.2 = j := fun h' => hij (h.symm.trans h')
      simp only [this, ↓reduceIte, mul_zero]
    · simp only [h, ↓reduceIte, star_zero, zero_mul]
