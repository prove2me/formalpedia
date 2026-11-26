-- Prove2me | solution 1 for FourierJacobi.Valuations.elementary_right_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:11.290694+00:00
-- url     : https://prove2.me/submissions/ad041e77-b9eb-4690-9e9d-ad3f6615cf85

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution (d b₁ b₂ c p q r s u w : K) (hd : d ≠ 0)
    (hsp : (firstColumnShape d b₁ b₂ c p q r s u w).transpose * J *
      firstColumnShape d b₁ b₂ c p q r s u w = J) :
    p * s - q * r = 1 ∧
      firstColumnShape d b₁ b₂ c p q r s u w * cartanEliminator d b₁ b₂ c =
        !![d, 0, 0, 0; 0, p, q, 0; 0, r, s, 0; 0, 0, 0, d⁻¹] := by
  have hdet := congrArg (fun A : Matrix (Fin 4) (Fin 4) K => A 1 2) hsp
  have hb₁ := congrArg (fun A : Matrix (Fin 4) (Fin 4) K => A 1 3) hsp
  have hb₂ := congrArg (fun A : Matrix (Fin 4) (Fin 4) K => A 2 3) hsp
  simp [firstColumnShape, J, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_succ] at hdet hb₁ hb₂
  have hdu : d * u - p * b₂ + q * b₁ = 0 := by
    field_simp at hb₁ hb₂
    linear_combination -d * u * hdet - p * hb₂ + q * hb₁
  have hdw : d * w - r * b₂ + s * b₁ = 0 := by
    field_simp at hb₁ hb₂
    linear_combination -d * w * hdet - r * hb₂ + s * hb₁
  constructor
  · linear_combination hdet
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [firstColumnShape, cartanEliminator, Matrix.mul_apply,
        Fin.sum_univ_succ] <;> field_simp <;>
      (solve | ring | linear_combination hdu | linear_combination hdw)
end FourierJacobi.Valuations
