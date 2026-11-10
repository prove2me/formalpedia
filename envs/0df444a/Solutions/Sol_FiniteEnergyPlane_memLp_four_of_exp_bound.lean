-- Prove2me | solution 1 for FiniteEnergyPlane.memLp_four_of_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T22:33:57.872495+00:00
-- url     : https://prove2.me/submissions/5c1ff3d7-4eaa-47bb-82a5-146a0f30c391

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib



/-!
# `L⁴` on the cylinder from exponential decay in `s` (source of the published
`FiniteEnergyPlane.memLp_four_of_exp_bound`)
-/

namespace FiniteEnergyPlane.QL4

open MeasureTheory Filter Set CauchyRiemannIndex

/-! ### `L⁴` on the cylinder from exponential decay in `s` -/

lemma exp_neg_abs_le_inv (κ : ℝ) (hκ : 0 < κ) (s : ℝ) :
    Real.exp (-(κ * |s|)) ≤ max 1 (2 / κ ^ 2) * (1 + s ^ 2)⁻¹ := by
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ κ * |s|)
  have hpos : 0 < 1 + s ^ 2 := by positivity
  rw [Real.exp_neg, ← div_eq_mul_inv, inv_le_comm₀ (Real.exp_pos _) (by positivity),
    inv_div]
  rw [div_le_iff₀ (by positivity)]
  have hM1 : 1 ≤ max 1 (2 / κ ^ 2) := le_max_left _ _
  have hM2 : 2 / κ ^ 2 ≤ max 1 (2 / κ ^ 2) := le_max_right _ _
  have hsq : (κ * |s|) ^ 2 = κ ^ 2 * s ^ 2 := by rw [mul_pow, sq_abs]
  have h2 : s ^ 2 ≤ max 1 (2 / κ ^ 2) * (κ ^ 2 * s ^ 2 / 2) := by
    have : s ^ 2 = (2 / κ ^ 2) * (κ ^ 2 * s ^ 2 / 2) := by field_simp
    nth_rewrite 1 [this]
    exact mul_le_mul_of_nonneg_right hM2 (by positivity)
  nlinarith [abs_nonneg s, mul_nonneg hκ.le (abs_nonneg s)]

theorem memLp_four_of_exp_bound {E : Type*} [NormedAddCommGroup E] (f : ℝ × ℝ → E)
    (hf : AEStronglyMeasurable f cylMeasure) (C κ : ℝ) (hκ : 0 < κ)
    (hb : ∀ s t, ‖f (s, t)‖ ≤ C * Real.exp (-(κ * |s|))) : MemLp f 4 cylMeasure := by
  set M := max 1 (2 / κ ^ 2)
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hb 0 0)
    simpa using this
  -- the dominating function `g (s, t) = C M (1 + s²)⁻¹ ^ (1/4)`-free form: use `L⁴` of a bound
  have hg : MemLp (fun q : ℝ × ℝ => C * M * ((1 + q.1 ^ 2)⁻¹) ^ ((1 : ℝ) / 4)) 4 cylMeasure := by
    have h1 : MemLp (fun s : ℝ => ((1 + s ^ 2)⁻¹) ^ ((1 : ℝ) / 4)) 4 volume := by
      have hmeas : AEStronglyMeasurable (fun s : ℝ => ((1 + s ^ 2)⁻¹) ^ ((1 : ℝ) / 4)) volume :=
        (((continuous_const.add (continuous_pow 2)).inv₀ (fun s => by show (1:ℝ) + s ^ 2 ≠ 0; positivity)).rpow_const
          (fun _ => Or.inr (by norm_num)) :
            Continuous fun s : ℝ => ((1 + s ^ 2)⁻¹) ^ ((1 : ℝ) / 4)).aestronglyMeasurable
      refine (integrable_norm_rpow_iff hmeas (by norm_num) (by norm_num)).1 ?_
      refine integrable_inv_one_add_sq.congr (Eventually.of_forall fun s => ?_)
      have hp : 0 ≤ (1 + s ^ 2)⁻¹ := by positivity
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp _)]
      rw [← Real.rpow_mul hp]
      norm_num
    have h2 := (h1.comp_fst (volume.restrict (Ico (0 : ℝ) 1))).const_mul (C * M)
    have hμ : cylMeasure = (volume : Measure ℝ).prod (volume.restrict (Ico (0 : ℝ) 1)) := by
      rw [cylMeasure, ← Measure.restrict_univ (μ := (volume : Measure ℝ)),
        Measure.prod_restrict, Measure.volume_eq_prod, Measure.restrict_univ]
    rw [hμ]
    simpa using h2
  refine hg.of_le hf (Eventually.of_forall fun q => ?_)
  obtain ⟨s, t⟩ := q
  have hp : 0 ≤ (1 + s ^ 2)⁻¹ := by positivity
  have hp' : 0 < (1 + s ^ 2)⁻¹ := by positivity
  have hr : (1 + s ^ 2)⁻¹ ≤ ((1 + s ^ 2)⁻¹) ^ ((1 : ℝ) / 4) := by
    have hle : (1 + s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg s])
    calc (1 + s ^ 2)⁻¹ = ((1 + s ^ 2)⁻¹) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge hp' hle (by norm_num)
  have hM : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  calc ‖f (s, t)‖ ≤ C * Real.exp (-(κ * |s|)) := hb s t
    _ ≤ C * (M * (1 + s ^ 2)⁻¹) := mul_le_mul_of_nonneg_left (exp_neg_abs_le_inv κ hκ s) hC
    _ ≤ C * (M * ((1 + s ^ 2)⁻¹) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr hM) hC
    _ = _ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring


end FiniteEnergyPlane.QL4

open FiniteEnergyPlane

open MeasureTheory CauchyRiemannIndex

theorem solution {E : Type*} [NormedAddCommGroup E] (f : ℝ × ℝ → E)
    (hf : AEStronglyMeasurable f cylMeasure) (C κ : ℝ) (hκ : 0 < κ)
    (hb : ∀ s t, ‖f (s, t)‖ ≤ C * Real.exp (-(κ * |s|))) : MemLp f 4 cylMeasure :=
  FiniteEnergyPlane.QL4.memLp_four_of_exp_bound f hf C κ hκ hb
