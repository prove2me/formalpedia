-- Prove2me | solution 1 for AvramDividend.Classical.esscher_nnreal_jump_mass_lt_drift_of_positive_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T12:44:58.447882+00:00
-- url     : https://prove2.me/submissions/22803032-c8d2-418c-8315-54e08dcaeadd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution
    (ν : Measure ℝ≥0) (δ φ q : ℝ)
    (hφ : 0 < φ) (hq : 0 < q)
    (hA : Integrable (fun z : ℝ≥0 =>
      (z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ν)
    (hJ : Integrable (fun z : ℝ≥0 =>
      1 - Real.exp (-(φ * (z : ℝ)))) ν)
    (hroot : δ * φ -
      (∫ z : ℝ≥0, 1 - Real.exp (-(φ * (z : ℝ))) ∂ν) = q) :
    (∫ z : ℝ≥0, (z : ℝ) * Real.exp (-(φ * (z : ℝ))) ∂ν) < δ := by
  have hAφ : Integrable
      (fun z : ℝ≥0 => φ * ((z : ℝ) * Real.exp (-(φ * (z : ℝ))))) ν :=
    hA.const_mul φ
  have hmono :
      (∫ z : ℝ≥0, φ * ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂ν) ≤
      (∫ z : ℝ≥0, 1 - Real.exp (-(φ * (z : ℝ))) ∂ν) := by
    apply integral_mono hAφ hJ
    intro z
    have hle : φ * (z : ℝ) ≤ Real.exp (φ * (z : ℝ)) - 1 := by
      linarith [Real.add_one_le_exp (φ * (z : ℝ))]
    have hprod :
        (φ * (z : ℝ)) * Real.exp (-(φ * (z : ℝ))) ≤
          (Real.exp (φ * (z : ℝ)) - 1) *
            Real.exp (-(φ * (z : ℝ))) :=
      mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    have he :
        Real.exp (φ * (z : ℝ)) * Real.exp (-(φ * (z : ℝ))) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      φ * ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) =
          (φ * (z : ℝ)) * Real.exp (-(φ * (z : ℝ))) := by ring
      _ ≤ (Real.exp (φ * (z : ℝ)) - 1) *
            Real.exp (-(φ * (z : ℝ))) := hprod
      _ = 1 - Real.exp (-(φ * (z : ℝ))) := by
        rw [sub_mul, he, one_mul]
  have hfactor :
      (∫ z : ℝ≥0, φ * ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂ν) =
        φ * (∫ z : ℝ≥0, (z : ℝ) * Real.exp (-(φ * (z : ℝ))) ∂ν) := by
    exact integral_const_mul φ (fun z : ℝ≥0 =>
      (z : ℝ) * Real.exp (-(φ * (z : ℝ))))
  have hstrict :
      φ * (∫ z : ℝ≥0, (z : ℝ) * Real.exp (-(φ * (z : ℝ))) ∂ν) <
        φ * δ := by
    calc
      φ * (∫ z : ℝ≥0, (z : ℝ) * Real.exp (-(φ * (z : ℝ))) ∂ν) =
        (∫ z : ℝ≥0, φ * ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂ν) :=
          hfactor.symm
      _ ≤ (∫ z : ℝ≥0, 1 - Real.exp (-(φ * (z : ℝ))) ∂ν) := hmono
      _ < φ * δ := by nlinarith [hroot, hq]
  by_contra hn
  have hle : δ ≤ (∫ z : ℝ≥0, (z : ℝ) * Real.exp (-(φ * (z : ℝ))) ∂ν) :=
    le_of_not_gt hn
  have hmul := mul_le_mul_of_nonneg_left hle hφ.le
  exact (not_le_of_gt hstrict) hmul
