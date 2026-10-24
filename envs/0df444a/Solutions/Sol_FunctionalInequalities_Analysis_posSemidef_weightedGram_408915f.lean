-- Prove2me | solution 1 for FunctionalInequalities.Analysis.posSemidef_weightedGram_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:42:08.92285+00:00
-- url     : https://prove2.me/submissions/6ee537af-d106-4102-ba14-5ae11fe82393

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open scoped MatrixOrder Kronecker
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Weighted Gram matrix**: for a positive semidefinite `A` and any family of matrices `T_i`, the matrix
`G_{ij} = Σ_{a,b,c,d} A_{ac} A_{bd} (T_i)_{ab} (T_j)_{cd} = (F (A ⊗ A) Fᵀ)_{ij}` is positive semidefinite. -/
theorem solution (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (T : κ → Matrix ι ι ℝ) :
    (Matrix.of fun i j => ∑ a, ∑ b, ∑ c, ∑ d,
      A a c * A b d * T i a b * T j c d).PosSemidef := by
  let F : Matrix κ (ι × ι) ℝ := fun i ab => T i ab.1 ab.2
  have h := (hA.kronecker hA).mul_mul_conjTranspose_same F
  have heq : F * (A ⊗ₖ A) * F.conjTranspose = Matrix.of (fun i j => ∑ a, ∑ b, ∑ c, ∑ d,
      A a c * A b d * T i a b * T j c d) := by
    rw [Matrix.mul_assoc]
    ext i j
    change (∑ ab : ι × ι, T i ab.1 ab.2 *
      (∑ cd : ι × ι, (A ab.1 cd.1 * A ab.2 cd.2) * T j cd.1 cd.2)) = _
    simp only [Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    apply Finset.sum_congr rfl
    intro b _hb
    apply Finset.sum_congr rfl
    intro c _hc
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  exact heq ▸ h
