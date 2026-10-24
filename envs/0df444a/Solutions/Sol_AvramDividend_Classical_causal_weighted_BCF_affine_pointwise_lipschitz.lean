-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_affine_pointwise_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:08:35.135194+00:00
-- url     : https://prove2.me/submissions/07b1c921-9323-4c30-aaae-2bf56dfe1248

import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_weighted_BCF_two_input_lipschitz_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The normalised weighted affine update is Lipschitz with constant m/a. -/
theorem solution
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    let m := ∫ t in Ioi (0 : ℝ),
      Real.exp (-w * t) * |β + K t| ∂volume
    0 ≤ m ∧ m < a ∧
      ∀ (f h : BoundedContinuousFunction ℝ≥0 ℝ) (x : ℝ), 0 ≤ x →
        |(Real.exp (-(w * x)) * (1 - (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
          (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume))) / a -
         (Real.exp (-(w * x)) * (1 - (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
          (Real.exp (w * s) * h ⟨max s 0, le_max_right s 0⟩) ∂volume))) / a| ≤
          ‖f - h‖ * (m / a) := by
  dsimp
  obtain ⟨hm0, hma, hbound⟩ :=
    causal_weighted_BCF_two_input_lipschitz_bound K a β w ha hw hK hsmall
  refine ⟨hm0, hma, ?_⟩
  intro f h x hx
  let If : ℝ := (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
          (Real.exp (w * s) * f ⟨max s 0, le_max_right s 0⟩) ∂volume)
  let Ih : ℝ := (∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) *
          (Real.exp (w * s) * h ⟨max s 0, le_max_right s 0⟩) ∂volume)
  have hIx : Real.exp (-(w * x)) * |If - Ih| ≤
      ‖f - h‖ * (∫ t in Ioi (0 : ℝ),
        Real.exp (-w * t) * |β + K t| ∂volume) := by
    rcases eq_or_lt_of_le hx with hzero | hpositive
    · subst x
      have hIf : If = 0 := by simp [If]
      have hIh : Ih = 0 := by simp [Ih]
      rw [hIf, hIh]
      simp only [sub_self, abs_zero, mul_zero]
      exact mul_nonneg (norm_nonneg _) hm0
    · exact hbound f h x x hpositive ⟨hpositive, le_refl x⟩
  have hAlg :
      (Real.exp (-(w * x)) * (1 - If)) / a -
        (Real.exp (-(w * x)) * (1 - Ih)) / a =
      -(Real.exp (-(w * x)) * (If - Ih)) / a := by ring
  calc
    |(Real.exp (-(w * x)) * (1 - If)) / a -
       (Real.exp (-(w * x)) * (1 - Ih)) / a| =
        Real.exp (-(w * x)) * |If - Ih| / a := by
          rw [hAlg, abs_div, abs_neg, abs_mul,
            abs_of_pos (Real.exp_pos _), abs_of_pos ha]
    _ ≤ (‖f - h‖ * (∫ t in Ioi (0 : ℝ),
        Real.exp (-w * t) * |β + K t| ∂volume)) / a :=
      div_le_div_of_nonneg_right hIx ha.le
    _ = ‖f - h‖ * ((∫ t in Ioi (0 : ℝ),
        Real.exp (-w * t) * |β + K t| ∂volume) / a) := by ring
