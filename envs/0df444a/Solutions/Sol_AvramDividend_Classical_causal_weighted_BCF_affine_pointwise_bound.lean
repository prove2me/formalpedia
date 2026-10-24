-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_affine_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:47:39.172184+00:00
-- url     : https://prove2.me/submissions/1e0d810d-86aa-45ef-be51-e882dcccef34

import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_explicit_kernel_mass_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The affine weighted causal operator is uniformly pointwise bounded. -/
theorem solution
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    let m := ∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * |β + K t| ∂volume
    0 ≤ m ∧ m < a ∧
      ∀ (f : BoundedContinuousFunction ℝ≥0 ℝ) (x : ℝ), 0 ≤ x →
        |(Real.exp (-(w * x)) *
          (1 - ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
            (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume)) / a| ≤
          (1 + ‖f‖ * m) / a := by
  dsimp
  obtain ⟨hm0, hma, hmass⟩ :=
    causal_weighted_BCF_explicit_kernel_mass_bound K a β w ha hw hK hsmall
  refine ⟨hm0, hma, ?_⟩
  intro f x hx
  let I : ℝ := ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
    (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume
  have hpos : 0 < Real.exp (-(w * x)) := Real.exp_pos _
  have he : Real.exp (-(w * x)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg hw.le hx)
  have hI : Real.exp (-(w * x)) * |I| ≤
      ‖f‖ * (∫ t in Ioi (0 : ℝ),
        Real.exp (-w * t) * |β + K t| ∂volume) := by
    rcases eq_or_lt_of_le hx with hzero | hpositive
    · subst x
      have hI0 : I = 0 := by simp [I]
      rw [hI0]
      simp only [abs_zero, mul_zero]
      exact mul_nonneg (norm_nonneg _) hm0
    · exact hmass f x x hpositive ⟨hpositive, le_refl x⟩
  have htri : |1 - I| ≤ 1 + |I| := by
    simpa only [sub_zero, zero_sub, abs_neg, abs_one] using
      (abs_sub_le (1 : ℝ) 0 I)
  have hscaled : Real.exp (-(w * x)) * |1 - I| ≤
      1 + ‖f‖ * (∫ t in Ioi (0 : ℝ),
        Real.exp (-w * t) * |β + K t| ∂volume) := calc
    _ ≤ Real.exp (-(w * x)) * (1 + |I|) :=
      mul_le_mul_of_nonneg_left htri hpos.le
    _ = Real.exp (-(w * x)) + Real.exp (-(w * x)) * |I| := by ring
    _ ≤ 1 + ‖f‖ * (∫ t in Ioi (0 : ℝ),
        Real.exp (-w * t) * |β + K t| ∂volume) :=
      add_le_add he hI
  calc
    |(Real.exp (-(w * x)) * (1 - I)) / a| =
        Real.exp (-(w * x)) * |1 - I| / a := by
          rw [abs_div, abs_mul, abs_of_pos hpos, abs_of_pos ha]
    _ ≤ (1 + ‖f‖ * (∫ t in Ioi (0 : ℝ),
        Real.exp (-w * t) * |β + K t| ∂volume)) / a :=
          div_le_div_of_nonneg_right hscaled ha.le
