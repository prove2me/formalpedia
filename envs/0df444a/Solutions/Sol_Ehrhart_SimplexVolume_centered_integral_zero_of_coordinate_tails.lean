-- Prove2me | solution 1 for Ehrhart.SimplexVolume.centered_integral_zero_of_coordinate_tails
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:11.14329+00:00
-- url     : https://prove2.me/submissions/364978cf-976a-40bd-8cb3-2e254c8521a8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.SimplexVolume
open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise
namespace Ehrhart.SimplexVolume
theorem _root_.solution
    {n : ℕ} (K : Set (Space n)) (hK : IsCompact K) (v : ℝ)
    (hT : ∀ y, y ∈ K ↔
      (∀ j, -(1 : ℝ) ≤ y j) ∧ (∑ j, y j) ≤ 1)
    (htail : ∀ (i : Fin n) {t : ℝ}, 0 ≤ t → t < (n : ℝ) + 1 →
      ((volume : Measure (Space n)).restrict K).real
        {y | t ≤ y i + 1} = (((n : ℝ) + 1) - t) ^ n * v) :
    (∫ y in K, y) = (0 : Space n) := by
  have hcoord : ∀ j : Fin n, Integrable (fun y : Space n => y j)
      ((volume : Measure (Space n)).restrict K) := fun j =>
    (continuous_apply j).continuousOn.integrableOn_compact hK
  have hone : Integrable (fun _ : Space n => (1 : ℝ))
      ((volume : Measure (Space n)).restrict K) :=
    continuous_const.continuousOn.integrableOn_compact hK
  ext i
  change (∫ y in K, y) i = 0
  rw [MeasureTheory.eval_integral hcoord i]
  have hsupport (y : Space n) (hy : y ∈ K) :
      0 ≤ y i + 1 ∧ y i + 1 ≤ (n : ℝ) + 1 := by
    have hy' := (hT y).mp hy
    have hnonneg (j : Fin n) : 0 ≤ y j + 1 := by linarith [hy'.1 j]
    refine ⟨hnonneg i, ?_⟩
    calc
      y i + 1 ≤ ∑ j, (y j + 1) :=
        Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      _ ≤ (n : ℝ) + 1 := by
        simpa [Finset.sum_add_distrib] using
          (show (∑ j, y j) + (n : ℝ) ≤ n + 1 by linarith [hy'.2])
  have hzero : 0 ≤ᵐ[(volume : Measure (Space n)).restrict K]
      fun y => y i + 1 := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact (hsupport y hy).1
  have hbound : (fun y : Space n => y i + 1)
      ≤ᵐ[(volume : Measure (Space n)).restrict K]
        fun _ => (n : ℝ) + 1 := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact (hsupport y hy).2
  have hvol : (volume : Measure (Space n)).real K =
      ((n : ℝ) + 1) ^ n * v := by
    have h := htail i (t := 0) (by norm_num) (by positivity)
    have hsub : K ⊆ {y : Space n | 0 ≤ y i + 1} :=
      fun y hy => (hsupport y hy).1
    rw [measureReal_restrict_apply' hK.measurableSet,
      Set.inter_eq_right.mpr hsub] at h
    simpa using h
  have hplus : Integrable (fun y : Space n => y i + 1)
      ((volume : Measure (Space n)).restrict K) :=
    (hcoord i).add hone
  have hmoment : (∫ y in K, y i + 1) =
      ((n : ℝ) + 1) ^ n * v := by
    rw [hplus.integral_eq_integral_Ioc_meas_le hzero hbound]
    calc
      (∫ t in Set.Ioc (0 : ℝ) ((n : ℝ) + 1),
        ((volume : Measure (Space n)).restrict K).real
          {y | t ≤ y i + 1}) =
          ∫ t in Set.Ioc (0 : ℝ) ((n : ℝ) + 1),
            (((n : ℝ) + 1) - t) ^ n * v := by
              apply setIntegral_congr_ae measurableSet_Ioc
              filter_upwards [(volume : Measure ℝ).ae_ne ((n : ℝ) + 1)]
                with t ht hmem
              exact htail i hmem.1.le (lt_of_le_of_ne hmem.2 ht)
      _ = (∫ t in Set.Ioc (0 : ℝ) ((n : ℝ) + 1),
            (((n : ℝ) + 1) - t) ^ n) * v := by
              exact integral_mul_const v
                (fun t : ℝ => (((n : ℝ) + 1) - t) ^ n)
      _ = ((n : ℝ) + 1) ^ n * v := by
        rw [← intervalIntegral.integral_of_le (by positivity),
          intervalIntegral.integral_comp_sub_left
            (fun t : ℝ => t ^ n) ((n : ℝ) + 1), integral_pow]
        simp [pow_succ, (by positivity : (n : ℝ) + 1 ≠ 0)]
  rw [integral_add (hcoord i) hone, integral_const,
    measureReal_restrict_apply_univ, smul_eq_mul, mul_one, hvol] at hmoment
  linarith
end Ehrhart.SimplexVolume
