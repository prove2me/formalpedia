-- Prove2me | solution 1 for D1Bound5.productFive_rankTwo_det_general
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:55:59.841275+00:00
-- url     : https://prove2.me/submissions/631b1b61-b5e4-4233-b3f1-db8782709f36

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_ProductFiveRankTwo_Definitions
import Theorems.Thm_D1Bound5_productFive_compressed_entry
import Theorems.Thm_D1Bound5_rankTwo_det_entries

section
open Matrix

namespace D1Bound5













/-- The exact rank-two determinant formula for the fifth-entry
Schur complement. No symmetry is assumed: both cross forms occur.
In the symmetric case the two cross forms coincide. -/
theorem _root_.solution
    (F : Matrix (Fin 4) (Fin 4) ℂ)
    (f w : Fin 4 → ℂ) (d : ℂ)
    (hF : F.det ≠ 0) (hd : d ≠ 0) :
    (F + productFiveColumns f w * productFiveRows f w d).det =
      F.det *
        (1 - ((w ⬝ᵥ (F⁻¹ *ᵥ f)) + (f ⬝ᵥ (F⁻¹ *ᵥ w))) / d +
          ((w ⬝ᵥ (F⁻¹ *ᵥ f)) * (f ⬝ᵥ (F⁻¹ *ᵥ w)) -
            (f ⬝ᵥ (F⁻¹ *ᵥ f)) * (w ⬝ᵥ (F⁻¹ *ᵥ w)) -
            (f ⬝ᵥ (F⁻¹ *ᵥ f))) / d^2) := by
  let k := w ⬝ᵥ (F⁻¹ *ᵥ f)
  let h := f ⬝ᵥ (F⁻¹ *ᵥ w)
  let p := f ⬝ᵥ (F⁻¹ *ᵥ f)
  let q := w ⬝ᵥ (F⁻¹ *ᵥ w)
  change _ = F.det * (1 - (k + h) / d + (k * h - p * q - p) / d^2)
  have h00 : (productFiveRows f w d * F⁻¹ *
        productFiveColumns f w) 0 0 = -k / d - p / d^2 := by
    simpa [k, p] using productFive_compressed_entry (F⁻¹) f w d 0 0
  have h01 : (productFiveRows f w d * F⁻¹ *
        productFiveColumns f w) 0 1 = -q / d - h / d^2 := by
    simpa [q, h] using productFive_compressed_entry (F⁻¹) f w d 0 1
  have h10 : (productFiveRows f w d * F⁻¹ *
        productFiveColumns f w) 1 0 = -p / d := by
    simpa [p] using productFive_compressed_entry (F⁻¹) f w d 1 0
  have h11 : (productFiveRows f w d * F⁻¹ *
        productFiveColumns f w) 1 1 = -h / d := by
    simpa [h] using productFive_compressed_entry (F⁻¹) f w d 1 1
  calc
    _ = F.det *
        ((1 + (productFiveRows f w d * F⁻¹ *
          productFiveColumns f w) 0 0) *
         (1 + (productFiveRows f w d * F⁻¹ *
          productFiveColumns f w) 1 1) -
         (productFiveRows f w d * F⁻¹ *
          productFiveColumns f w) 0 1 *
         (productFiveRows f w d * F⁻¹ *
          productFiveColumns f w) 1 0) :=
          rankTwo_det_entries F _ _ hF
    _ = _ := by
      rw [h00, h11, h01, h10]
      field_simp [hd]
      ring











end D1Bound5
end
