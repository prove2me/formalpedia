-- Prove2me | solution 1 for BianchiIX.norm_euler_le_of_signedRowSum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:34:17.288398+00:00
-- url     : https://prove2.me/submissions/1ce2889e-48b8-4621-a0f8-fc3c70d0f2d9

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp


noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]


theorem solution {A : Matrix ι ι ℝ} {ρ h : ℝ}
    (hA : ∀ i, signedRowSum A i ≤ ρ) (hh : 0 ≤ h)
    (hdiag : ∀ i, 0 ≤ 1 + h * A i i) (x : ι → ℝ) :
    ‖x + h • A.mulVec x‖ ≤ (1 + h * ρ) * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  have hcoord (j : ι) : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  have hsum : |∑ j ∈ Finset.univ.erase i, A i j * x j| ≤
      (∑ j ∈ Finset.univ.erase i, |A i j|) * ‖x‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase i, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.univ.erase i, |A i j| * ‖x‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hcoord j) (abs_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hid : (x + h • A.mulVec x) i =
      (1 + h * A i i) * x i + h * ∑ j ∈ Finset.univ.erase i, A i j * x j := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    rw [← Finset.add_sum_erase Finset.univ (fun j => A i j * x j) (Finset.mem_univ i)]
    ring
  rw [hid, Real.norm_eq_abs]
  calc
    _ ≤ |(1 + h * A i i) * x i| + |h * ∑ j ∈ Finset.univ.erase i, A i j * x j| := abs_add_le _ _
    _ = (1 + h * A i i) * |x i| + h * |∑ j ∈ Finset.univ.erase i, A i j * x j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hdiag i), abs_of_nonneg hh]
    _ ≤ (1 + h * A i i) * ‖x‖ + h * ((∑ j ∈ Finset.univ.erase i, |A i j|) * ‖x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (hcoord i) (hdiag i)) (mul_le_mul_of_nonneg_left hsum hh)
    _ = (1 + h * signedRowSum A i) * ‖x‖ := by unfold signedRowSum; ring
    _ ≤ (1 + h * ρ) * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left (hA i) hh)) (norm_nonneg _)
