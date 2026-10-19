-- Prove2me | solution 1 for Ehrhart.RadialPhysicalInverseSquareRootEnergy.complexPositiveInverseSquareRootAction_pairing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/9a21e12f-0223-42e3-8ee1-4a7dc6b278df

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.RadialPhysicalInverseSquareRootEnergy
open Set Function Filter MeasureTheory Matrix
open RadialSchurBlock
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  InnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology ContDiff
namespace Ehrhart.RadialPhysicalInverseSquareRootEnergy
theorem _root_.solution
    {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (b : Fin n → ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _
      (Matrix.toEuclideanLin ((CFC.sqrt A)⁻¹)
        (WithLp.toLp 2 (star b)))
      (Matrix.toEuclideanLin (CFC.sqrt A) v) =
      b ⬝ᵥ (fun i : Fin n => v i) := by
  have hroot := hA.isStrictlyPositive.sqrt.posDef
  have hdet : IsUnit (CFC.sqrt A).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hroot.isUnit
  calc
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (Matrix.toEuclideanLin ((CFC.sqrt A)⁻¹)
          (WithLp.toLp 2 (star b)))
        (Matrix.toEuclideanLin (CFC.sqrt A) v) =
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (WithLp.toLp 2 (star b))
        (Matrix.toEuclideanLin ((CFC.sqrt A)⁻¹)
          (Matrix.toEuclideanLin (CFC.sqrt A) v)) :=
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr
        hroot.inv.isHermitian)
        (WithLp.toLp 2 (star b))
        (Matrix.toEuclideanLin (CFC.sqrt A) v)
    _ = @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (WithLp.toLp 2 (star b)) v := by
      rw [complexEuclideanMatrixAction_mul,
        Matrix.nonsing_inv_mul _ hdet]
      congr 1
      ext i
      simp
    _ = b ⬝ᵥ (fun i : Fin n => v i) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        ((fun i : Fin n => v i) ⬝ᵥ star (star b)) =
          b ⬝ᵥ (fun i : Fin n => v i)
      rw [star_star, dotProduct_comm]
end Ehrhart.RadialPhysicalInverseSquareRootEnergy
