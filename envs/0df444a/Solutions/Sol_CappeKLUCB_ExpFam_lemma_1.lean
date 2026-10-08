-- Prove2me | solution 1 for CappeKLUCB.ExpFam.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:07:55.022458+00:00
-- url     : https://prove2.me/submissions/81c9125f-dd75-4347-a789-08393cc2de22

import Mathlib
import Definitions.Def_CappeKLUCB_ExpFam_Setting

set_option autoImplicit false

namespace P4d6dc7c7

lemma pt_le (l x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp (l * x) ≤ 1 - x + x * Real.exp l := by
  have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ l) (sub_nonneg.2 h1) h0
    (by ring : (1 - x) + x = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at this
  rw [mul_comm l x]
  linarith

lemma bern_le (l m : ℝ) (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    1 - m + m * Real.exp l ≤ Real.exp (l * m + 2 * l ^ 2) := by
  rcases le_or_gt (|l|) 1 with hl | hl
  · have h := abs_le.1 (Real.abs_exp_sub_one_sub_id_le hl)
    have hpos : 0 ≤ Real.exp l - 1 - l := by linarith [Real.add_one_le_exp l]
    have hq : m * (Real.exp l - 1) ≤ l * m + 2 * l ^ 2 := by
      have : m * (Real.exp l - 1 - l) ≤ 1 * (Real.exp l - 1 - l) :=
        mul_le_mul_of_nonneg_right h1 hpos
      nlinarith [sq_nonneg l]
    calc 1 - m + m * Real.exp l = m * (Real.exp l - 1) + 1 := by ring
      _ ≤ Real.exp (m * (Real.exp l - 1)) := Real.add_one_le_exp _
      _ ≤ _ := Real.exp_le_exp.2 hq
  · rcases lt_abs.1 hl with hl | hl
    · have he : 1 ≤ Real.exp l := Real.one_le_exp (by linarith)
      calc 1 - m + m * Real.exp l ≤ Real.exp l := by nlinarith
        _ ≤ _ := Real.exp_le_exp.2 (by nlinarith)
    · have he : 0 < Real.exp l := Real.exp_pos l
      have he1 : Real.exp l ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      calc 1 - m + m * Real.exp l ≤ 1 := by nlinarith
        _ ≤ _ := Real.one_le_exp (by nlinarith)

end P4d6dc7c7

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic OptimalBAI.OptProportions in
theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (l : ℝ) :
    ∫ x, Real.exp (l * x) ∂ν ≤ 1 - (∫ x, x ∂ν) + (∫ x, x ∂ν) * Real.exp l ∧
      1 - (∫ x, x ∂ν) + (∫ x, x ∂ν) * Real.exp l ≤
        Real.exp (l * (∫ x, x ∂ν) + 2 * l ^ 2) := by
  have hae : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1 := mem_ae_iff.2 hν
  have hix : Integrable (fun x : ℝ => x) ν := by
    refine Integrable.of_bound (measurable_id.aestronglyMeasurable) 1 ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hie : Integrable (fun x : ℝ => Real.exp (l * x)) ν := by
    refine Integrable.of_bound ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable) (Real.exp |l|) ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    have : |l * x| ≤ |l| := by
      rw [abs_mul]
      have : |x| ≤ 1 := by rw [abs_le]; exact ⟨by linarith [hx.1], hx.2⟩
      nlinarith [abs_nonneg l, abs_nonneg x]
    linarith [le_abs_self (l * x)]
  have hm0 : 0 ≤ ∫ x, x ∂ν := integral_nonneg_of_ae (by
    filter_upwards [hae] with x hx; exact hx.1)
  have hm1 : (∫ x, x ∂ν) ≤ 1 := by
    have : (∫ x, x ∂ν) ≤ ∫ _x, (1 : ℝ) ∂ν :=
      integral_mono_ae hix (integrable_const _) (by
        filter_upwards [hae] with x hx; exact hx.2)
    simpa using this
  refine ⟨?_, P4d6dc7c7.bern_le l _ hm0 hm1⟩
  have hint : Integrable (fun x : ℝ => 1 - x + x * Real.exp l) ν :=
    ((integrable_const _).sub hix).add (hix.mul_const _)
  calc ∫ x, Real.exp (l * x) ∂ν ≤ ∫ x, (1 - x + x * Real.exp l) ∂ν :=
        integral_mono_ae hie hint (by
          filter_upwards [hae] with x hx; exact P4d6dc7c7.pt_le l x hx.1 hx.2)
    _ = 1 - (∫ x, x ∂ν) + (∫ x, x ∂ν) * Real.exp l := by
        have h1 : Integrable (fun x : ℝ => (1 : ℝ) - x) ν := (integrable_const _).sub hix
        rw [integral_add (f := fun x : ℝ => (1 : ℝ) - x) (g := fun x : ℝ => x * Real.exp l)
          h1 (hix.mul_const _),
          integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x) (integrable_const _) hix,
          integral_mul_const]
        simp
