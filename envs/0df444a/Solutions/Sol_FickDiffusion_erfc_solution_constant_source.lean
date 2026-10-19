-- Prove2me | solution 1 for FickDiffusion.erfc_solution_constant_source
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:08:43.467352+00:00
-- url     : https://prove2.me/submissions/3e343ff9-7e23-463d-a035-63a8d3673766

import Mathlib
import Definitions.Def_FickDiffusion_defs
open Real Filter Topology MeasureTheory FickDiffusion

namespace FickErfc

noncomputable def g (s : ℝ) : ℝ := Real.exp (-s ^ 2)

lemma g_integrable : Integrable g := by
  have := integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  show Integrable (fun s : ℝ => Real.exp (-s ^ 2))
  simpa using this

lemma g_continuous : Continuous g := by unfold g; fun_prop

lemma I0 : ∫ s in Set.Ioi (0 : ℝ), g s = Real.sqrt π / 2 := by
  have := integral_gaussian_Ioi 1
  simpa [g] using this

lemma Iic0 : ∫ s in Set.Iic (0 : ℝ), g s = Real.sqrt π / 2 := by
  have htot : ∫ s, g s = Real.sqrt π := by
    have := integral_gaussian 1
    simpa [g] using this
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (b := (0 : ℝ)) (μ := volume)
    g_integrable.integrableOn g_integrable.integrableOn
  rw [htot, I0] at hsplit
  linarith

lemma erfc_eq (u : ℝ) : erfc u = 2 / Real.sqrt π * (Real.sqrt π / 2 - ∫ s in (0 : ℝ)..u, g s) := by
  unfold erfc
  have h := intervalIntegral.integral_Ioi_sub_Ioi' (a := (0 : ℝ)) (b := u) (μ := volume)
    g_integrable.integrableOn g_integrable.integrableOn
  rw [I0] at h
  have : ∫ s in Set.Ioi u, Real.exp (-s ^ 2) = Real.sqrt π / 2 - ∫ s in (0 : ℝ)..u, g s := by
    have e : ∫ s in Set.Ioi u, Real.exp (-s ^ 2) = ∫ s in Set.Ioi u, g s := rfl
    rw [e]; linarith
  rw [this]

lemma erfc_hasDerivAt (u : ℝ) :
    HasDerivAt erfc (-(2 / Real.sqrt π) * Real.exp (-u ^ 2)) u := by
  have hI : HasDerivAt (fun v => ∫ s in (0 : ℝ)..v, g s) (g u) u :=
    intervalIntegral.integral_hasDerivAt_right (g_continuous.intervalIntegrable _ _)
      (g_continuous.stronglyMeasurableAtFilter _ _) g_continuous.continuousAt
  have h := (hI.const_sub (Real.sqrt π / 2)).const_mul (2 / Real.sqrt π)
  have hfun : erfc = fun v => 2 / Real.sqrt π * (Real.sqrt π / 2 - ∫ s in (0 : ℝ)..v, g s) :=
    funext erfc_eq
  rw [hfun]
  exact h.congr_deriv (by unfold g; ring)

lemma erfc_zero : erfc 0 = 1 := by
  rw [erfc_eq, intervalIntegral.integral_same, sub_zero]
  have : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

lemma erfc_atTop : Tendsto erfc atTop (𝓝 0) := by
  have h := intervalIntegral_tendsto_integral_Ioi (μ := volume) 0 g_integrable.integrableOn
    tendsto_id
  rw [I0] at h
  have := (h.const_sub (Real.sqrt π / 2)).const_mul (2 / Real.sqrt π)
  rw [sub_self, mul_zero] at this
  refine this.congr fun u => ?_
  rw [erfc_eq]; rfl

lemma erfc_atBot : Tendsto erfc atBot (𝓝 2) := by
  have h := intervalIntegral_tendsto_integral_Iic (μ := volume) 0 g_integrable.integrableOn
    tendsto_id
  rw [Iic0] at h
  have := (h.const_add (Real.sqrt π / 2)).const_mul (2 / Real.sqrt π)
  have hpi : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [show 2 / Real.sqrt π * (Real.sqrt π / 2 + Real.sqrt π / 2) = 2 by field_simp; ring] at this
  refine this.congr fun u => ?_
  rw [erfc_eq, intervalIntegral.integral_symm]
  simp only [id]
  ring

end FickErfc

namespace FickErfc

lemma pde (c D : ℝ) (hD : 0 < D) (x t : ℝ) (ht : 0 < t) :
    deriv (fun s => c * erfc (x / (2 * Real.sqrt (D * s)))) t =
      D * deriv (fun y => deriv (fun z => c * erfc (z / (2 * Real.sqrt (D * t)))) y) x := by
  have hDt : 0 < D * t := mul_pos hD ht
  have hsq : 0 < Real.sqrt (D * t) := Real.sqrt_pos.mpr hDt
  set w := 2 * Real.sqrt (D * t) with hw
  have hw0 : 0 < w := by positivity
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  -- first space derivative
  have hd1 : ∀ y : ℝ, HasDerivAt (fun z => c * erfc (z / w))
      (c * (-(2 / Real.sqrt π) * Real.exp (-(y / w) ^ 2) * (1 / w))) y := by
    intro y
    have h := (erfc_hasDerivAt (y / w)).comp y ((hasDerivAt_id' y).div_const w)
    exact (h.const_mul c).congr_deriv (by ring)
  have hderiv1 : deriv (fun z => c * erfc (z / w)) =
      fun y => c * (-(2 / Real.sqrt π) * Real.exp (-(y / w) ^ 2) * (1 / w)) :=
    funext fun y => (hd1 y).deriv
  -- second space derivative
  have hd2 : HasDerivAt (fun y => c * (-(2 / Real.sqrt π) * Real.exp (-(y / w) ^ 2) * (1 / w)))
      (c * (-(2 / Real.sqrt π) * (Real.exp (-(x / w) ^ 2) * (-(2 * (x / w) * (1 / w)))) * (1 / w))) x := by
    have h1 : HasDerivAt (fun y => -(y / w) ^ 2) (-(2 * (x / w) * (1 / w))) x := by
      have := (((hasDerivAt_id' x).div_const w).pow 2).neg
      exact this.congr_deriv (by norm_num <;> ring)
    have := ((h1.exp.const_mul (-(2 / Real.sqrt π))).mul_const (1 / w)).const_mul c
    exact this.congr_deriv (by ring)
  rw [hderiv1, hd2.deriv]
  -- time derivative
  have hws : HasDerivAt (fun s => 2 * Real.sqrt (D * s)) (2 * (D / (2 * Real.sqrt (D * t)))) t := by
    have := (((hasDerivAt_id' t).const_mul D).sqrt hDt.ne').const_mul 2
    exact this.congr_deriv (by ring)
  have hu : HasDerivAt (fun s => x / (2 * Real.sqrt (D * s)))
      (-(x * (2 * (D / (2 * Real.sqrt (D * t))))) / (2 * Real.sqrt (D * t)) ^ 2) t := by
    have := (hasDerivAt_const t x).div hws (by positivity)
    exact this.congr_deriv (by ring)
  have ht2 := ((erfc_hasDerivAt (x / (2 * Real.sqrt (D * t)))).comp t hu).const_mul c
  have ht3 : HasDerivAt (fun s => c * erfc (x / (2 * Real.sqrt (D * s))))
      (c * (-(2 / Real.sqrt π) * Real.exp (-(x / (2 * Real.sqrt (D * t))) ^ 2) *
        (-(x * (2 * (D / (2 * Real.sqrt (D * t))))) / (2 * Real.sqrt (D * t)) ^ 2))) t := ht2
  rw [ht3.deriv, hw]
  have hs2 : Real.sqrt (D * t) ^ 2 = D * t := Real.sq_sqrt hDt.le
  field_simp

lemma tendsto_arg_pos (D x : ℝ) (hD : 0 < D) (hx : 0 < x) :
    Tendsto (fun t => x / (2 * Real.sqrt (D * t))) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun t => 2 * Real.sqrt (D * t)) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun t => 2 * Real.sqrt (D * t)) (𝓝 0) (𝓝 (2 * Real.sqrt (D * 0))) :=
        (Continuous.tendsto (by fun_prop) 0)
      simp only [mul_zero, Real.sqrt_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Set.mem_Ioi.mpr (by have : 0 < D * t := mul_pos hD ht; positivity)
  have h2 := h1.inv_tendsto_nhdsGT_zero
  have h3 := h2.const_mul_atTop hx
  refine h3.congr fun t => ?_
  simp [div_eq_mul_inv]

lemma tendsto_arg_neg (D x : ℝ) (hD : 0 < D) (hx : x < 0) :
    Tendsto (fun t => x / (2 * Real.sqrt (D * t))) (𝓝[>] 0) atBot := by
  have h := tendsto_arg_pos D (-x) hD (by linarith)
  refine (tendsto_neg_atTop_atBot.comp h).congr fun t => ?_
  simp [neg_div]

end FickErfc

open FickErfc in
theorem solution (D n₀ : ℝ) (hD : 0 < D) :
    (∀ x t : ℝ, 0 < t →
      deriv (fun s => n₀ * erfc (x / (2 * Real.sqrt (D * s)))) t =
        D * deriv (fun y => deriv (fun z => n₀ * erfc (z / (2 * Real.sqrt (D * t)))) y) x) ∧
    (∀ t : ℝ, 0 < t → n₀ * erfc (0 / (2 * Real.sqrt (D * t))) = n₀) ∧
    (∀ x : ℝ, 0 < x →
      Tendsto (fun t => n₀ * erfc (x / (2 * Real.sqrt (D * t)))) (𝓝[>] 0) (𝓝 0)) := by
  refine ⟨fun x t ht => pde n₀ D hD x t ht, fun t _ => ?_, fun x hx => ?_⟩
  · rw [zero_div, erfc_zero, mul_one]
  · have := (erfc_atTop.comp (tendsto_arg_pos D x hD hx)).const_mul n₀
    rw [mul_zero] at this
    exact this
