-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_quadraticFloor_of_posDef_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:20:57.0841+00:00
-- url     : https://prove2.me/submissions/aa5cf6ab-4351-480a-bd3a-902ce90076b3

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
section Floor
open Matrix Finset
open scoped RealInnerProductSpace Matrix.Norms.L2Operator
variable [DecidableEq ι]
/-- A Loewner scalar lower bound gives a quadratic floor. -/
theorem FunctionalInequalities.Analysis.quadraticFloor_of_algebraMap_le {S : Matrix ι ι ℝ} {a : ℝ}
    (h : algebraMap ℝ (Matrix ι ι ℝ) a ≤ S) : QuadraticFloor S a := by
  have hp : (S - algebraMap ℝ (Matrix ι ι ℝ) a).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)
  intro v
  have hv := hp.dotProduct_mulVec_nonneg v
  rw [Algebra.algebraMap_eq_smul_one, sub_mulVec, dotProduct_sub,
    smul_mulVec, one_mulVec, dotProduct_smul] at hv
  simp only [star_trivial, smul_eq_mul] at hv
  have he : v ⬝ᵥ v = ∑ i, (v i) ^ 2 := by simp only [dotProduct, pow_two]
  rw [he] at hv
  linarith
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- A positive definite matrix has a positive quadratic floor (the empty index type gives floor `1`
without any spectrum argument). -/
theorem solution {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    ∃ a : ℝ, 0 < a ∧ FunctionalInequalities.Analysis.QuadraticFloor S a := by
  classical
  by_cases h : Nonempty ι
  · let : Nonempty ι := h
    obtain ⟨a, ha, hle⟩ :=
      (CFC.exists_pos_algebraMap_le_iff hS.isStrictlyPositive.isSelfAdjoint).mpr
        (fun x hx => hS.isStrictlyPositive.spectrum_pos hx)
    exact ⟨a, ha, FunctionalInequalities.Analysis.quadraticFloor_of_algebraMap_le hle⟩
  · have : IsEmpty ι := not_nonempty_iff.mp h
    refine ⟨1, by norm_num, ?_⟩
    intro v
    simp only [dotProduct, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, le_refl]
