-- Prove2me | solution 1 for CouplingConstantRG.isMuRunning_inv_relation
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T16:07:53.386003+00:00
-- url     : https://prove2.me/submissions/b766e57b-3d30-4ffc-96d3-11e73e082ebc

import Mathlib

import Definitions.Def_CouplingConstantRGDefs

set_option linter.unusedVariables false

open CouplingConstantRG Real Set

theorem solution (b μ₀ T α₀ : ℝ) (α : ℝ → ℝ) (hμ₀ : 0 < μ₀) (hT : μ₀ ≤ T) (hα₀ : 0 < α₀)
    (h₀ : α μ₀ = α₀) (hα : IsMuRunning b α (Icc μ₀ T)) :
    ∀ μ ∈ Icc μ₀ T, α μ * (1 - b * α₀ * log (μ / μ₀)) = α₀ := by
  classical
  let φ : ℝ → ℝ := fun μ => α μ * (1 - b * α₀ * log (μ / μ₀))
  let δ : ℝ → ℝ := fun μ => φ μ - α₀
  have hδ0 : δ μ₀ = 0 := by
    simp [δ, φ, h₀, div_self hμ₀.ne', log_one]
  have hcontα : ContinuousOn α (Icc μ₀ T) :=
    fun μ hμ => (hα μ hμ).continuousAt.continuousWithinAt
  have hlogc : ContinuousOn (fun μ => log (μ / μ₀)) (Icc μ₀ T) := by
    refine ContinuousOn.log (continuousOn_id.div_const μ₀) ?_
    intro μ hμ
    exact (div_pos (lt_of_lt_of_le hμ₀ hμ.1) hμ₀).ne'
  have hcontφ : ContinuousOn φ (Icc μ₀ T) :=
    hcontα.mul (continuousOn_const.sub ((continuousOn_const.mul hlogc)))
  have hcontδ : ContinuousOn δ (Icc μ₀ T) := hcontφ.sub continuousOn_const
  have himg : IsCompact ((fun x => ‖x‖) '' (α '' Icc μ₀ T)) :=
    (isCompact_Icc.image_of_continuousOn hcontα).image_of_continuousOn
      (continuous_norm.continuousOn)
  have hbdd : BddAbove ((fun x => ‖x‖) '' (α '' Icc μ₀ T)) := himg.bddAbove
  obtain ⟨C0, hC0⟩ := hbdd
  let C : ℝ := max C0 1
  have hCle : ∀ μ ∈ Icc μ₀ T, ‖α μ‖ ≤ C := by
    intro μ hμ
    have hmem : ‖α μ‖ ∈ (fun x => ‖x‖) '' (α '' Icc μ₀ T) :=
      mem_image_of_mem _ (mem_image_of_mem _ hμ)
    exact (hC0 hmem).trans (le_max_left _ _)
  let K : ℝ := |b| * C / μ₀
  have hderiv :
      ∀ μ ∈ Ico μ₀ T, HasDerivWithinAt δ ((b * α μ / μ) * δ μ) (Ici μ) μ := by
    intro μ hμ
    have hμI : μ ∈ Icc μ₀ T := ⟨hμ.1, le_of_lt hμ.2⟩
    have hμpos : 0 < μ := lt_of_lt_of_le hμ₀ hμ.1
    have hαd : HasDerivAt α (b * α μ ^ 2 / μ) μ := hα μ hμI
    have hquot : HasDerivAt (fun t => t / μ₀) (1 / μ₀) μ :=
      (hasDerivAt_id μ).div_const μ₀
    have hlog0 : HasDerivAt (fun t => log (t / μ₀)) ((μ / μ₀)⁻¹ * (1 / μ₀)) μ := by
      have hcomp := (hasDerivAt_log (div_pos hμpos hμ₀).ne').comp μ hquot
      have hfun : (fun t => log (t / μ₀)) = log ∘ fun t => t / μ₀ := by funext t; rfl
      rw [hfun]
      exact hcomp
    have hlog : HasDerivAt (fun t => log (t / μ₀)) (1 / μ) μ := by
      have heq : (μ / μ₀)⁻¹ * (1 / μ₀) = 1 / μ := by field_simp [hμpos.ne', hμ₀.ne']
      rw [← heq]
      exact hlog0
    have hinner : HasDerivAt (fun t => b * α₀ * log (t / μ₀)) (b * α₀ * (1 / μ)) μ :=
      hlog.const_mul (b * α₀)
    have hg := (hasDerivAt_const μ (1 : ℝ)).sub hinner
    have hφ := hαd.mul hg
    have hδ0at := hφ.sub (hasDerivAt_const μ α₀)
    have hfun :
        (α * ((fun _ : ℝ => (1 : ℝ)) - fun t => b * α₀ * log (t / μ₀)) - fun _ => α₀) = δ := by
      funext t
      simp [δ, φ]
    have hder :
        (b * α μ ^ 2 / μ) * ((fun _ : ℝ => (1 : ℝ)) - fun t => b * α₀ * log (t / μ₀)) μ +
            α μ * (0 - b * α₀ * (1 / μ)) - 0 =
          (b * α μ / μ) * δ μ := by
      simp [δ, φ]
      field_simp [hμpos.ne']
      ring
    rw [hfun, hder] at hδ0at
    exact hδ0at.hasDerivWithinAt
  have hbound : ∀ μ ∈ Ico μ₀ T, ‖(b * α μ / μ) * δ μ‖ ≤ K * ‖δ μ‖ := by
    intro μ hμ
    have hμI : μ ∈ Icc μ₀ T := ⟨hμ.1, le_of_lt hμ.2⟩
    have hμpos : 0 < μ := lt_of_lt_of_le hμ₀ hμ.1
    have hαle : |α μ| ≤ C := by simpa [Real.norm_eq_abs] using hCle μ hμI
    have hcoef : |b * α μ / μ| ≤ K := by
      have habs : |b * α μ / μ| = |b| * |α μ| / μ := by
        rw [abs_div, abs_mul, abs_of_pos hμpos]
      rw [habs]
      have h1 : |b| * |α μ| / μ ≤ |b| * C / μ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hαle (abs_nonneg _)) (le_of_lt hμpos)
      have hCnonneg : 0 ≤ |b| * C := mul_nonneg (abs_nonneg _) (le_trans zero_le_one (le_max_right _ _))
      have h2 : |b| * C / μ ≤ |b| * C / μ₀ :=
        div_le_div_of_nonneg_left hCnonneg hμ₀ hμ.1
      exact h1.trans h2
    have hnorm : ‖(b * α μ / μ) * δ μ‖ = |b * α μ / μ| * |δ μ| := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [hnorm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg (δ μ))
  have hzero :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := δ)
      (f' := fun μ => (b * α μ / μ) * δ μ) (K := K) (a := μ₀) (b := T)
      hcontδ hderiv hδ0 hbound
  intro μ hμ
  have hδμ : δ μ = 0 := hzero μ hμ
  have : φ μ - α₀ = 0 := by simpa [δ] using hδμ
  simpa [φ] using eq_of_sub_eq_zero this
