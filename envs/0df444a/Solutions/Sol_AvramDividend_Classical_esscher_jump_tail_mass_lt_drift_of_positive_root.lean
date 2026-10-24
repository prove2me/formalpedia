-- Prove2me | solution 1 for AvramDividend.Classical.esscher_jump_tail_mass_lt_drift_of_positive_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:44:21.866395+00:00
-- url     : https://prove2.me/submissions/2530d249-c07c-4650-89b3-50768b799bf0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped ENNReal

/-!
A positive Esscher root implies subcriticality of its jump-tail kernel.
The pointwise estimate is integrated before using the strict root identity.
-/
theorem solution
    (ν : Measure ℝ) (δ φ q : ℝ)
    (hφ : 0 < φ) (hq : 0 < q)
    (hA : IntegrableOn (fun z : ℝ => z * Real.exp (-(φ * z)))
      (Ioi (0 : ℝ)) ν)
    (hJ : IntegrableOn (fun z : ℝ => 1 - Real.exp (-(φ * z)))
      (Ioi (0 : ℝ)) ν)
    (hroot : δ * φ -
      (∫ z in Ioi (0 : ℝ), 1 - Real.exp (-(φ * z)) ∂ν) = q) :
    (∫ z in Ioi (0 : ℝ), z * Real.exp (-(φ * z)) ∂ν) < δ := by
  have hAφ : IntegrableOn
      (fun z : ℝ => φ * (z * Real.exp (-(φ * z))))
      (Ioi (0 : ℝ)) ν := hA.const_mul φ
  have hmono :
      (∫ z in Ioi (0 : ℝ), φ * (z * Real.exp (-(φ * z))) ∂ν) ≤
      (∫ z in Ioi (0 : ℝ), 1 - Real.exp (-(φ * z)) ∂ν) := by
    apply setIntegral_mono_on hAφ hJ measurableSet_Ioi
    intro z hz
    have hle : φ * z ≤ Real.exp (φ * z) - 1 := by
      linarith [Real.add_one_le_exp (φ * z)]
    have hepos : 0 ≤ Real.exp (-(φ * z)) :=
      (Real.exp_pos _).le
    have hprod :
        (φ * z) * Real.exp (-(φ * z)) ≤
          (Real.exp (φ * z) - 1) * Real.exp (-(φ * z)) :=
      mul_le_mul_of_nonneg_right hle hepos
    have he :
        Real.exp (φ * z) * Real.exp (-(φ * z)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hvalue :
        (φ * z) * Real.exp (-(φ * z)) ≤
          1 - Real.exp (-(φ * z)) := by
      calc
        _ ≤ (Real.exp (φ * z) - 1) * Real.exp (-(φ * z)) := hprod
        _ = 1 - Real.exp (-(φ * z)) := by
          rw [sub_mul, he, one_mul]
    simpa only [mul_assoc] using hvalue
  have hfactor :
      (∫ z in Ioi (0 : ℝ), φ * (z * Real.exp (-(φ * z))) ∂ν) =
        φ * (∫ z in Ioi (0 : ℝ),
          z * Real.exp (-(φ * z)) ∂ν) := by
    exact integral_const_mul φ (fun z : ℝ => z * Real.exp (-(φ * z)))
  have hscaled :
      φ * (∫ z in Ioi (0 : ℝ), z * Real.exp (-(φ * z)) ∂ν) <
        φ * δ := by
    calc
      _ = (∫ z in Ioi (0 : ℝ), φ * (z * Real.exp (-(φ * z))) ∂ν) :=
        hfactor.symm
      _ ≤ (∫ z in Ioi (0 : ℝ), 1 - Real.exp (-(φ * z)) ∂ν) :=
        hmono
      _ < φ * δ := by
        nlinarith [hroot, hq]
  exact lt_of_mul_lt_mul_left hscaled hφ.le
