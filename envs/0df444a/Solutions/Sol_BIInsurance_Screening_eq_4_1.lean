-- Prove2me | solution 1 for BIInsurance.Screening.eq_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T20:58:15.397285+00:00
-- url     : https://prove2.me/submissions/3fd1caa5-8b61-4386-aee3-4f534d4884c0

import Mathlib
import Definitions.Def_BIInsurance_Screening_Logistic

open MeasureTheory Set Filter Topology

namespace BIInsurance.Screening

/-- Integrability on `Iic a` of a nonnegative derivative of a function with a limit at `-∞`. -/
lemma integrableOn_Iic_deriv_of_nonneg_aux {G g : ℝ → ℝ} {a l : ℝ}
    (hderiv : ∀ t ∈ Iic a, HasDerivAt G (g t) t) (hpos : ∀ t ∈ Iic a, 0 ≤ g t)
    (hG : Tendsto G atBot (𝓝 l)) : IntegrableOn g (Iic a) := by
  have hcont : ContinuousOn G (Iic a) := fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
  have hint : ∀ y, y ≤ a → IntegrableOn g (Ioc y a) := by
    intro y hy
    have := intervalIntegral.integrableOn_deriv_of_nonneg (g := G) (g' := g) (a := y) (b := a)
      (hcont.mono (Icc_subset_Iic_self)) (fun t ht => hderiv t (le_of_lt ht.2))
      (fun t ht => hpos t (le_of_lt ht.2))
    exact this
  refine integrableOn_Iic_of_intervalIntegral_norm_tendsto (G a - l) a (l := atBot)
    (a := fun y => min y a) (fun y => hint _ (min_le_right _ _)) ?_ ?_
  · exact tendsto_atBot_mono (fun y => min_le_left y a) tendsto_id
  · apply Tendsto.congr' _ ((hG.comp (tendsto_atBot_mono (fun y => min_le_left y a)
      tendsto_id)).const_sub (G a))
    filter_upwards [Iic_mem_atBot a] with y hy
    have hy' : min y a = y := min_eq_left hy
    simp only [Function.comp, hy']
    rw [intervalIntegral.integral_of_le hy]
    rw [setIntegral_congr_fun measurableSet_Ioc (g := g)
      (fun t ht => by simp [Real.norm_eq_abs, abs_of_nonneg (hpos t ht.2)])]
    rw [← intervalIntegral.integral_of_le hy]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy
      (hcont.mono Icc_subset_Iic_self) (fun t ht => hderiv t (le_of_lt ht.2))]
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hy]
    exact hint y hy

/-- Logistic CDF. -/
noncomputable def lcdf (γ m t : ℝ) : ℝ := 1 / (1 + Real.exp (-(t - m) / γ))

lemma hasDerivAt_lcdf (γ m t : ℝ) (hγ : 0 < γ) :
    HasDerivAt (lcdf γ m) (logisticPDF γ m t) t := by
  have h1 : HasDerivAt (fun t => -(t - m) / γ) (-1 / γ) t := by
    have := ((hasDerivAt_id t).sub_const m).neg.div_const γ
    simpa using this
  have h2 := (h1.exp.const_add 1).inv (by positivity)
  unfold lcdf logisticPDF
  have : (fun t => 1 / (1 + Real.exp (-(t - m) / γ))) = fun t => (1 + Real.exp (-(t - m) / γ))⁻¹ := by
    funext t; simp
  rw [this]
  refine h2.congr_deriv ?_
  have : 0 < 1 + Real.exp (-(t - m) / γ) := by positivity
  field_simp

lemma hasDerivAt_lsp (γ m t : ℝ) (hγ : 0 < γ) :
    HasDerivAt (fun t => γ * Real.log (1 + Real.exp ((t - m) / γ))) (lcdf γ m t) t := by
  have h1 : HasDerivAt (fun t => (t - m) / γ) (1 / γ) t := by
    simpa using ((hasDerivAt_id t).sub_const m).div_const γ
  have h2 := ((h1.exp.const_add 1).log (by positivity)).const_mul γ
  refine h2.congr_deriv ?_
  unfold lcdf
  have he : Real.exp (-(t - m) / γ) = (Real.exp ((t - m) / γ))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [he]
  have : 0 < Real.exp ((t - m) / γ) := Real.exp_pos _
  field_simp
  ring

lemma lcdf_le_exp (γ m t : ℝ) : lcdf γ m t ≤ Real.exp ((t - m) / γ) := by
  unfold lcdf
  have he : Real.exp (-(t - m) / γ) = (Real.exp ((t - m) / γ))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [he]
  have : 0 < Real.exp ((t - m) / γ) := Real.exp_pos _
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith

lemma lcdf_pos (γ m t : ℝ) : 0 < lcdf γ m t := by
  unfold lcdf; positivity

lemma tendsto_lcdf_atTop (γ m : ℝ) (hγ : 0 < γ) : Tendsto (lcdf γ m) atTop (𝓝 1) := by
  have h1 : Tendsto (fun t : ℝ => -(t - m) / γ) atTop atBot := by
    have : Tendsto (fun t : ℝ => (t - m) / γ) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-m) tendsto_id).atTop_div_const hγ |>.congr
        (fun t => by simp [sub_eq_add_neg])
    exact (tendsto_neg_atTop_atBot.comp this).congr (fun t => by simp only [Function.comp]; ring)
  have h2 := (Real.tendsto_exp_atBot.comp h1).const_add 1
  have h3 := h2.inv₀ (by norm_num)
  simp only [add_zero, inv_one] at h3
  refine h3.congr (fun t => ?_)
  simp [lcdf, Function.comp]

lemma tendsto_lcdf_atBot (γ m : ℝ) (hγ : 0 < γ) : Tendsto (lcdf γ m) atBot (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (t - m) / γ) atBot atBot :=
    (tendsto_atBot_add_const_right _ (-m) tendsto_id).atBot_div_const hγ |>.congr
      (fun t => by simp [sub_eq_add_neg])
  have h2 := Real.tendsto_exp_atBot.comp h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun t => (lcdf_pos γ m t).le) (fun t => lcdf_le_exp γ m t)

lemma tendsto_lsp_atBot (γ m : ℝ) (hγ : 0 < γ) :
    Tendsto (fun t => γ * Real.log (1 + Real.exp ((t - m) / γ))) atBot (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (t - m) / γ) atBot atBot :=
    (tendsto_atBot_add_const_right _ (-m) tendsto_id).atBot_div_const hγ |>.congr
      (fun t => by simp [sub_eq_add_neg])
  have h2 := (Real.tendsto_exp_atBot.comp h1).const_add 1
  have h3 := (Real.continuousAt_log (by norm_num : (1 + 0 : ℝ) ≠ 0)).tendsto.comp h2
  have h4 := h3.const_mul γ
  simpa using h4

lemma tendsto_lin_lcdf_atBot (γ m x : ℝ) (hγ : 0 < γ) :
    Tendsto (fun t => (x - t) * lcdf γ m t) atBot (𝓝 0) := by
  -- v = (m - t)/γ → ∞, and (x - t) = (x - m) + γ v
  have hv : Tendsto (fun t : ℝ => (m - t) / γ) atBot atTop := by
    have : Tendsto (fun t : ℝ => m - t) atBot atTop :=
      tendsto_atTop_add_const_left _ m tendsto_neg_atBot_atTop |>.congr (fun t => by ring)
    exact this.atTop_div_const hγ
  have hA : Tendsto (fun v : ℝ => ((x - m) + γ * v) * Real.exp (-v)) atTop (𝓝 0) := by
    have e1 := Real.tendsto_exp_neg_atTop_nhds_zero
    have e2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have := (e1.const_mul (x - m)).add (e2.const_mul γ)
    simp only [pow_one, mul_zero, add_zero] at this
    refine this.congr (fun v => by ring)
  have hB := hA.comp hv
  have hB' : Tendsto (fun t => (x - t) * Real.exp ((t - m) / γ)) atBot (𝓝 0) := by
    refine hB.congr (fun t => ?_)
    simp only [Function.comp]
    have : -((m - t) / γ) = (t - m) / γ := by ring
    rw [this]; congr 1; field_simp; ring
  -- squeeze on t ≤ x
  have hlow : Tendsto (fun _ : ℝ => (0:ℝ)) atBot (𝓝 0) := tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hB' ?_ ?_
  · filter_upwards [Iic_mem_atBot x] with t ht
    exact mul_nonneg (by linarith [ht.out]) (lcdf_pos γ m t).le
  · filter_upwards [Iic_mem_atBot x] with t ht
    exact mul_le_mul_of_nonneg_left (lcdf_le_exp γ m t) (by linarith [ht.out])

lemma logisticPDF_nonneg (γ m t : ℝ) (hγ : 0 < γ) : 0 ≤ logisticPDF γ m t := by
  unfold logisticPDF; positivity

theorem eq_4_1_main (γ m x : ℝ) (hγ : 0 < γ) :
    MeasureTheory.Integrable (fun t => min t x * logisticPDF γ m t) ∧
      expSales γ m x = x + m - γ * Real.log (Real.exp (x / γ) + Real.exp (m / γ)) := by
  set f := logisticPDF γ m with hfdef
  set F := lcdf γ m with hFdef
  set Lg : ℝ → ℝ := fun t => γ * Real.log (1 + Real.exp ((t - m) / γ)) with hLg
  set H : ℝ → ℝ := fun t => (x - t) * F t + Lg t with hH
  have hFd : ∀ t, HasDerivAt F (f t) t := fun t => hasDerivAt_lcdf γ m t hγ
  have hLd : ∀ t, HasDerivAt Lg (F t) t := fun t => hasDerivAt_lsp γ m t hγ
  have hHd : ∀ t, HasDerivAt H ((x - t) * f t) t := by
    intro t
    have h1 : HasDerivAt (fun t => x - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub x
    have := (h1.mul (hFd t)).add (hLd t)
    refine this.congr_deriv ?_
    ring
  have hHlim : Tendsto H atBot (𝓝 0) := by
    have := (tendsto_lin_lcdf_atBot γ m x hγ).add (tendsto_lsp_atBot γ m hγ)
    simpa using this
  have hfpos : ∀ t, 0 ≤ f t := fun t => logisticPDF_nonneg γ m t hγ
  have i1 : IntegrableOn f (Iic x) :=
    integrableOn_Iic_deriv_of_nonneg_aux (fun t _ => hFd t) (fun t _ => hfpos t)
      (tendsto_lcdf_atBot γ m hγ)
  have i2 : IntegrableOn (fun t => (x - t) * f t) (Iic x) :=
    integrableOn_Iic_deriv_of_nonneg_aux (fun t _ => hHd t)
      (fun t ht => mul_nonneg (by linarith [ht.out]) (hfpos t)) hHlim
  have i3 : IntegrableOn f (Ioi x) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun t _ => hFd t) (fun t _ => hfpos t)
      (tendsto_lcdf_atTop γ m hγ)
  have eqIic : EqOn (fun t => x * f t - (x - t) * f t) (fun t => min t x * f t) (Iic x) := by
    intro t ht
    simp only [min_eq_left (show t ≤ x from ht)]
    ring
  have eqIoi : EqOn (fun t => x * f t) (fun t => min t x * f t) (Ioi x) := by
    intro t ht
    simp only [min_eq_right (le_of_lt (show x < t from ht))]
  have gI : IntegrableOn (fun t => min t x * f t) (Iic x) :=
    IntegrableOn.congr_fun ((i1.const_mul x).sub i2) eqIic measurableSet_Iic
  have gO : IntegrableOn (fun t => min t x * f t) (Ioi x) :=
    IntegrableOn.congr_fun (i3.const_mul x) eqIoi measurableSet_Ioi
  have gint : Integrable (fun t => min t x * f t) := by
    have := gI.union gO
    rw [Iic_union_Ioi] at this
    exact integrableOn_univ.mp this
  refine ⟨gint, ?_⟩
  have hsplit : expSales γ m x = (∫ t in Iic x, min t x * f t) + ∫ t in Ioi x, min t x * f t := by
    unfold expSales
    rw [← setIntegral_univ, ← Iic_union_Ioi (a := x),
      setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi gI gO]
  have hI : (∫ t in Iic x, min t x * f t) = x * F x - H x := by
    rw [← setIntegral_congr_fun measurableSet_Iic eqIic, integral_sub (i1.const_mul x) i2,
      integral_const_mul,
      integral_Iic_of_hasDerivAt_of_tendsto' (fun t _ => hFd t) i1 (tendsto_lcdf_atBot γ m hγ),
      integral_Iic_of_hasDerivAt_of_tendsto' (fun t _ => hHd t) i2 hHlim]
    ring
  have hO : (∫ t in Ioi x, min t x * f t) = x * (1 - F x) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi eqIoi, integral_const_mul,
      integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hFd t) i3 (tendsto_lcdf_atTop γ m hγ)]
  rw [hsplit, hI, hO]
  simp only [hH, hLg]
  have hexp : Real.exp (x / γ) + Real.exp (m / γ) = Real.exp (m / γ) * (1 + Real.exp ((x - m) / γ)) := by
    rw [mul_add, mul_one, ← Real.exp_add]
    have : m / γ + (x - m) / γ = x / γ := by field_simp; ring
    rw [this]; ring
  rw [hexp, Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  field_simp
  ring

end BIInsurance.Screening

open BIInsurance.Screening in
theorem solution (γ m x : ℝ) (hγ : 0 < γ) :
    MeasureTheory.Integrable (fun t => min t x * logisticPDF γ m t) ∧
      expSales γ m x = x + m - γ * Real.log (Real.exp (x / γ) + Real.exp (m / γ)) :=
  eq_4_1_main γ m x hγ
