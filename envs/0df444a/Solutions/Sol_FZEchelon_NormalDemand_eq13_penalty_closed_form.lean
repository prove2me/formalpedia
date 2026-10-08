-- Prove2me | solution 1 for FZEchelon.NormalDemand.eq13_penalty_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T01:24:58.7047+00:00
-- url     : https://prove2.me/submissions/60017259-2a64-4b84-a22b-c13864ef4bed

import Mathlib
import Definitions.Def_FZEchelon_NormalDemand_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real Filter Topology

open FZEchelon.NormalDemand in
lemma q46_pdf_eq (y : ℝ) :
    stdNormalPDF y = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
  simp only [stdNormalPDF, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  congr 2
  ring

open FZEchelon.NormalDemand in
lemma q46_pdf_fun : stdNormalPDF
    = fun y => (Real.sqrt (2 * π))⁻¹ * Real.exp (-(y ^ 2 / 2)) := by
  funext y; exact q46_pdf_eq y

open FZEchelon.NormalDemand in
lemma q46_pdf_cont : Continuous stdNormalPDF := by
  rw [q46_pdf_fun]
  fun_prop

open FZEchelon.NormalDemand in
lemma q46_pdf_deriv (y : ℝ) :
    HasDerivAt stdNormalPDF (-y * stdNormalPDF y) y := by
  have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2 / 2)) (-y) y :=
    (((hasDerivAt_pow 2 y).div_const 2).neg).congr_deriv (by norm_num)
  have h2 := (h1.exp).const_mul (Real.sqrt (2 * π))⁻¹
  rw [q46_pdf_fun]
  exact h2.congr_deriv (by ring)

lemma q46_real_eq (s : Set ℝ) :
    (gaussianReal 0 1).real s = ∫ v in s, gaussianPDFReal 0 1 v := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg_of_ae
      (ae_of_all _ (fun _ => gaussianPDFReal_nonneg _ _ _)))]

open FZEchelon.NormalDemand in
lemma q46_cdf_deriv (y : ℝ) :
    HasDerivAt stdNormalCDF (stdNormalPDF y) y := by
  show HasDerivAt (fun u => cdf (gaussianReal 0 1) u) (gaussianPDFReal 0 1 y) y
  have hI : ∀ u, cdf (gaussianReal 0 1) u = ∫ v in Set.Iic u, gaussianPDFReal 0 1 v := by
    intro u; rw [cdf_eq_real, q46_real_eq]
  have hint : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  have key : (fun u => cdf (gaussianReal 0 1) u)
      = fun u => cdf (gaussianReal 0 1) 0 + ∫ t in (0:ℝ)..u, gaussianPDFReal 0 1 t := by
    funext u
    rw [← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn, hI u, hI 0]
    ring
  rw [key]
  exact ((q46_pdf_cont.integral_hasStrictDerivAt 0 y).hasDerivAt).const_add
    (cdf (gaussianReal 0 1) 0)

open FZEchelon.NormalDemand in
lemma q46_cdf_cont : Continuous stdNormalCDF :=
  continuous_iff_continuousAt.2 fun y => (q46_cdf_deriv y).continuousAt

open FZEchelon.NormalDemand in
lemma q46_pdf_nonneg (y : ℝ) : 0 ≤ stdNormalPDF y := gaussianPDFReal_nonneg _ _ _

open FZEchelon.NormalDemand in
lemma q46_pdf_le (y : ℝ) : stdNormalPDF y ≤ 1 := by
  rw [q46_pdf_eq]
  have h1 : (Real.sqrt (2 * π))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    rw [Real.one_le_sqrt]
    nlinarith [Real.pi_gt_three]
  have h2 : Real.exp (-(y ^ 2 / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg y]
  exact mul_le_one₀ h1 (Real.exp_pos _).le h2

open FZEchelon.NormalDemand in
lemma q46_cdf_nonneg (y : ℝ) : 0 ≤ stdNormalCDF y := cdf_nonneg _ _

open FZEchelon.NormalDemand in
lemma q46_cdf_le (y : ℝ) : stdNormalCDF y ≤ 1 := cdf_le_one _ _

open FZEchelon.NormalDemand in
lemma q46_pdf_neg (y : ℝ) : stdNormalPDF (-y) = stdNormalPDF y := by
  rw [q46_pdf_eq, q46_pdf_eq, neg_sq]

open FZEchelon.NormalDemand in
lemma q46_pdf_atTop : Tendsto stdNormalPDF atTop (𝓝 0) := by
  have ht : Tendsto (fun y : ℝ => y ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul (Real.sqrt (2 * π))⁻¹
  rw [mul_zero] at h
  rw [q46_pdf_fun]
  exact h

open FZEchelon.NormalDemand in
lemma q46_pdf_atBot : Tendsto stdNormalPDF atBot (𝓝 0) := by
  have h := q46_pdf_atTop.comp tendsto_neg_atBot_atTop
  have he : stdNormalPDF ∘ (fun y : ℝ => -y) = stdNormalPDF := by
    funext y; simp [q46_pdf_neg]
  rwa [he] at h

open FZEchelon.NormalDemand in
lemma q46_cdf_atBot : Tendsto stdNormalCDF atBot (𝓝 0) := tendsto_cdf_atBot _

open FZEchelon.NormalDemand in
lemma q46_int_pdf : Integrable stdNormalPDF := integrable_gaussianPDFReal 0 1

open FZEchelon.NormalDemand in
lemma q46_int_mul_pdf : Integrable (fun y => y * stdNormalPDF y) := by
  have h := (integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).const_mul
    (Real.sqrt (2 * π))⁻¹
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [q46_pdf_eq]
  ring_nf

lemma q46_bdd (f g : ℝ → ℝ) (hg : Integrable g) (hf : Continuous f) (hb : ∀ y, |f y| ≤ 1) :
    Integrable (fun y => f y * g y) :=
  hg.bdd_mul hf.aestronglyMeasurable (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hb y)

open FZEchelon.NormalDemand in
lemma q46_abs_pdf (y : ℝ) : |stdNormalPDF y| ≤ 1 := by
  rw [abs_of_nonneg (q46_pdf_nonneg y)]; exact q46_pdf_le y

open FZEchelon.NormalDemand in
lemma q46_abs_cdf (y : ℝ) : |stdNormalCDF y| ≤ 1 := by
  rw [abs_of_nonneg (q46_cdf_nonneg y)]; exact q46_cdf_le y

open FZEchelon.NormalDemand in
lemma q46_aff_deriv (f f' : ℝ → ℝ) (hf : ∀ y, HasDerivAt f (f' y) y) (γ δ z : ℝ) :
    HasDerivAt (fun z => f (γ * z + δ)) (f' (γ * z + δ) * γ) z := by
  have h1 : HasDerivAt (fun z : ℝ => γ * z + δ) γ z :=
    (((hasDerivAt_id z).const_mul γ).add_const δ).congr_deriv (by simp)
  exact (hf (γ * z + δ)).comp z h1

open FZEchelon.NormalDemand in
lemma q46_int_aff (γ δ : ℝ) (hγ : γ ≠ 0) :
    Integrable (fun z => stdNormalPDF (γ * z + δ)) := by
  have h := (q46_int_pdf.comp_add_right δ).comp_mul_left' hγ
  exact h

open FZEchelon.NormalDemand in
lemma q46_ftc_aff (γ δ τ : ℝ) (hγ : 0 < γ) :
    ∫ z in Set.Iic τ, stdNormalPDF (γ * z + δ) = stdNormalCDF (γ * τ + δ) / γ := by
  have hd : ∀ z, HasDerivAt (fun z => stdNormalCDF (γ * z + δ) / γ) (stdNormalPDF (γ * z + δ)) z := by
    intro z
    have := (q46_aff_deriv stdNormalCDF stdNormalPDF q46_cdf_deriv γ δ z).div_const γ
    exact this.congr_deriv (by rw [mul_div_assoc, div_self hγ.ne', mul_one])
  have hlim : Tendsto (fun z => stdNormalCDF (γ * z + δ) / γ) atBot (𝓝 0) := by
    have h1 : Tendsto (fun z : ℝ => γ * z + δ) atBot atBot :=
      tendsto_atBot_add_const_right _ δ (tendsto_id.const_mul_atBot hγ)
    have := (q46_cdf_atBot.comp h1).div_const γ
    simpa using this
  rw [integral_Iic_of_hasDerivAt_of_tendsto (hd τ).continuousAt.continuousWithinAt
    (fun z _ => hd z) (q46_int_aff γ δ hγ.ne').integrableOn hlim, sub_zero]

open FZEchelon.NormalDemand in
lemma q46_int_cdf (τ : ℝ) : ∫ z in Set.Iic τ, stdNormalPDF z = stdNormalCDF τ := by
  have := q46_ftc_aff 1 0 τ one_pos
  simpa using this

open FZEchelon.NormalDemand in
lemma q46_i1 (τ : ℝ) : Integrable (fun z => (τ - z) * stdNormalPDF z) := by
  refine ((q46_int_pdf.const_mul τ).sub q46_int_mul_pdf).congr (ae_of_all _ fun z => ?_)
  simp only [Pi.sub_apply]
  ring

open FZEchelon.NormalDemand in
lemma q46_i2 (α β : ℝ) : Integrable (fun z => stdNormalCDF (α + β * z) * stdNormalPDF z) :=
  q46_bdd (fun z => stdNormalCDF (α + β * z)) _ q46_int_pdf (q46_cdf_cont.comp (continuous_const.add (continuous_const.mul continuous_id)))
    (fun z => q46_abs_cdf _)

open FZEchelon.NormalDemand in
lemma q46_i4 (α β : ℝ) : Integrable (fun z => stdNormalPDF (α + β * z) * stdNormalPDF z) :=
  q46_bdd (fun z => stdNormalPDF (α + β * z)) _ q46_int_pdf (q46_pdf_cont.comp (continuous_const.add (continuous_const.mul continuous_id)))
    (fun z => q46_abs_pdf _)

open FZEchelon.NormalDemand in
lemma q46_i3 (α β : ℝ) : Integrable (fun z =>
    (z * stdNormalCDF (α + β * z) - β * stdNormalPDF (α + β * z)) * stdNormalPDF z) := by
  have h1 := q46_bdd (fun z => stdNormalCDF (α + β * z)) _ q46_int_mul_pdf
    (q46_cdf_cont.comp (continuous_const.add (continuous_const.mul continuous_id))) (fun z => q46_abs_cdf _)
  refine (h1.sub ((q46_i4 α β).const_mul β)).congr (ae_of_all _ fun z => ?_)
  simp only [Pi.sub_apply]
  ring

open FZEchelon.NormalDemand in
lemma q46_L1 (τ : ℝ) : ∫ z in Set.Iic τ, (τ - z) * stdNormalPDF z = Theta τ := by
  have hd : ∀ z, HasDerivAt (fun z => τ * stdNormalCDF z + stdNormalPDF z)
      ((τ - z) * stdNormalPDF z) z := by
    intro z
    exact (((q46_cdf_deriv z).const_mul τ).add (q46_pdf_deriv z)).congr_deriv (by ring)
  have hlim : Tendsto (fun z => τ * stdNormalCDF z + stdNormalPDF z) atBot (𝓝 0) := by
    have := (q46_cdf_atBot.const_mul τ).add q46_pdf_atBot
    simpa using this
  rw [integral_Iic_of_hasDerivAt_of_tendsto (hd τ).continuousAt.continuousWithinAt
    (fun z _ => hd z) (q46_i1 τ).integrableOn hlim, sub_zero]
  rfl

open FZEchelon.NormalDemand in
lemma q46_L2 (α β τ : ℝ) (hβ : 0 < β) :
    ∫ z in Set.Iic τ, (z * stdNormalCDF (α + β * z) - β * stdNormalPDF (α + β * z)) * stdNormalPDF z
      = -(stdNormalCDF (α + β * τ) * stdNormalPDF τ) := by
  have hd : ∀ z, HasDerivAt (fun z => -(stdNormalCDF (α + β * z) * stdNormalPDF z))
      ((z * stdNormalCDF (α + β * z) - β * stdNormalPDF (α + β * z)) * stdNormalPDF z) z := by
    intro z
    have hc : HasDerivAt (fun z => stdNormalCDF (α + β * z)) (stdNormalPDF (α + β * z) * β) z := by
      have := q46_aff_deriv stdNormalCDF stdNormalPDF q46_cdf_deriv β α z
      simpa [add_comm] using this
    exact ((hc.mul (q46_pdf_deriv z)).neg).congr_deriv (by ring)
  have hlim : Tendsto (fun z => -(stdNormalCDF (α + β * z) * stdNormalPDF z)) atBot (𝓝 0) := by
    have h1 : Tendsto (fun z : ℝ => α + β * z) atBot atBot :=
      tendsto_atBot_add_const_left _ α (tendsto_id.const_mul_atBot hβ)
    have := ((q46_cdf_atBot.comp h1).mul q46_pdf_atBot).neg
    simpa using this
  rw [integral_Iic_of_hasDerivAt_of_tendsto (hd τ).continuousAt.continuousWithinAt
    (fun z _ => hd z) (q46_i3 α β).integrableOn hlim, sub_zero]

open FZEchelon.NormalDemand in
lemma q46_prod_pdf (α β γ z : ℝ) (hγ : 0 < γ) (hγ2 : γ ^ 2 = 1 + β ^ 2) :
    stdNormalPDF (α + β * z) * stdNormalPDF z
      = stdNormalPDF (α / γ) * stdNormalPDF (γ * z + α * β / γ) := by
  rw [q46_pdf_eq, q46_pdf_eq, q46_pdf_eq, q46_pdf_eq]
  have hE : -((α + β * z) ^ 2 / 2) + -(z ^ 2 / 2)
      = -((α / γ) ^ 2 / 2) + -((γ * z + α * β / γ) ^ 2 / 2) := by
    field_simp
    linear_combination (γ ^ 2 * z ^ 2 - α ^ 2) * hγ2
  calc (Real.sqrt (2 * π))⁻¹ * Real.exp (-((α + β * z) ^ 2 / 2))
        * ((Real.sqrt (2 * π))⁻¹ * Real.exp (-(z ^ 2 / 2)))
      = (Real.sqrt (2 * π))⁻¹ * (Real.sqrt (2 * π))⁻¹
          * Real.exp (-((α + β * z) ^ 2 / 2) + -(z ^ 2 / 2)) := by rw [Real.exp_add]; ring
    _ = (Real.sqrt (2 * π))⁻¹ * (Real.sqrt (2 * π))⁻¹
          * Real.exp (-((α / γ) ^ 2 / 2) + -((γ * z + α * β / γ) ^ 2 / 2)) := by rw [hE]
    _ = _ := by rw [Real.exp_add]; ring

open FZEchelon.NormalDemand in
lemma q46_L3 (α β γ τ : ℝ) (hγ : 0 < γ) (hγ2 : γ ^ 2 = 1 + β ^ 2) :
    ∫ z in Set.Iic τ, stdNormalPDF (α + β * z) * stdNormalPDF z
      = stdNormalPDF (α / γ) * (stdNormalCDF (γ * τ + α * β / γ) / γ) := by
  have h : (fun z => stdNormalPDF (α + β * z) * stdNormalPDF z)
      = fun z => stdNormalPDF (α / γ) * stdNormalPDF (γ * z + α * β / γ) := by
    funext z; exact q46_prod_pdf α β γ z hγ hγ2
  rw [h, integral_const_mul, q46_ftc_aff γ _ τ hγ]

open FZEchelon.NormalDemand in
lemma q46_biv_pdf (ρ k s t : ℝ) (hk : 0 < k) (hk2 : k ^ 2 = 1 - ρ ^ 2) :
    bivNormalPDF ρ s t = stdNormalPDF s * (stdNormalPDF (k⁻¹ * t + -(ρ * s / k)) / k) := by
  unfold bivNormalPDF
  rw [← hk2, Real.sqrt_sq hk.le, q46_pdf_eq, q46_pdf_eq]
  have hs : Real.sqrt (2 * π) * Real.sqrt (2 * π) = 2 * π := Real.mul_self_sqrt (by positivity)
  have hsp : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hE : -(s ^ 2 - 2 * ρ * s * t + t ^ 2) / (2 * k ^ 2)
      = -(s ^ 2 / 2) + -((k⁻¹ * t + -(ρ * s / k)) ^ 2 / 2) := by
    rw [hk2]
    have : (1 - ρ ^ 2) ≠ 0 := by rw [← hk2]; positivity
    rw [← hk2] at this ⊢
    field_simp
    linear_combination (s ^ 2) * hk2
  have hc : (2 * π * k)⁻¹ = (Real.sqrt (2 * π))⁻¹ * (Real.sqrt (2 * π))⁻¹ / k := by
    rw [div_eq_mul_inv, ← mul_inv, ← mul_inv, hs]
  rw [hE, Real.exp_add, hc]
  ring

open FZEchelon.NormalDemand in
lemma q46_inner (ρ k s ξ : ℝ) (hk : 0 < k) (hk2 : k ^ 2 = 1 - ρ ^ 2) :
    ∫ t in Set.Iic ξ, bivNormalPDF ρ s t = stdNormalPDF s * stdNormalCDF ((ξ - ρ * s) / k) := by
  have h : (fun t => bivNormalPDF ρ s t)
      = fun t => (stdNormalPDF s / k) * stdNormalPDF (k⁻¹ * t + -(ρ * s / k)) := by
    funext t; rw [q46_biv_pdf ρ k s t hk hk2]; ring
  rw [h, integral_const_mul, q46_ftc_aff _ _ ξ (inv_pos.2 hk)]
  have : k⁻¹ * ξ + -(ρ * s / k) = (ξ - ρ * s) / k := by ring
  rw [this]
  field_simp

lemma q46_emb (m a : ℝ) (ha : 0 < a) : MeasurableEmbedding (fun z : ℝ => a * z + m) :=
  ((Homeomorph.mulLeft₀ a ha.ne').trans (Homeomorph.addRight m)).measurableEmbedding

lemma q46_gauss_map (m s : ℝ) :
    gaussianReal m (Real.toNNReal (s ^ 2)) = (gaussianReal 0 1).map (fun z => s * z + m) := by
  have h : gaussianReal m (Real.toNNReal (s ^ 2))
      = ((gaussianReal 0 1).map (s * ·)).map (· + m) := by
    rw [gaussianReal_map_const_mul, gaussianReal_map_add_const]
    congr 1
    · simp
    · ext
      simp [sq_nonneg]
  rw [h, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

open FZEchelon.NormalDemand in
lemma q46_gsub (m a : ℝ) (ha : 0 < a) (g : ℝ → ℝ) :
    ∫ t, g t ∂(InventoryControl.newsboyDemand m a) = ∫ z, stdNormalPDF z * g (m + a * z) := by
  rw [InventoryControl.newsboyDemand_eq, q46_gauss_map m a, (q46_emb m a ha).integral_map,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  congr 1
  funext z
  simp only [smul_eq_mul]
  rw [add_comm m]
  rfl

open FZEchelon.NormalDemand in
lemma q46_gsub' (m a : ℝ) (ha : 0 < a) (g : ℝ → ℝ) :
    ∫ t, g t ∂(InventoryControl.newsboyDemand m a) = ∫ z, stdNormalPDF z * g (m - a * z) := by
  rw [q46_gsub m a ha, ← integral_neg_eq_self]
  congr 1
  funext z
  rw [q46_pdf_neg]
  congr 2
  ring

open FZEchelon.NormalDemand in
lemma q46_posTheta (m b y : ℝ) (hb : 0 < b) :
    ∫ t, max (y - t) 0 ∂(InventoryControl.newsboyDemand m b) = b * Theta ((y - m) / b) := by
  rw [q46_gsub m b hb]
  have h : (fun z => stdNormalPDF z * max (y - (m + b * z)) 0)
      = (Set.Iic ((y - m) / b)).indicator (fun z => b * (((y - m) / b - z) * stdNormalPDF z)) := by
    funext z
    by_cases hz : z ≤ (y - m) / b
    · rw [Set.indicator_of_mem (show z ∈ Set.Iic ((y - m) / b) from hz)]
      have h1 : z * b ≤ y - m := (le_div_iff₀ hb).1 hz
      rw [max_eq_left (by linarith)]
      field_simp
      ring
    · rw [Set.indicator_of_notMem (show z ∉ Set.Iic ((y - m) / b) from hz)]
      have h1 : y - m < z * b := (div_lt_iff₀ hb).1 (lt_of_not_ge hz)
      rw [max_eq_right (by linarith), mul_zero]
  rw [h, integral_indicator measurableSet_Iic, integral_const_mul, q46_L1]

open FZEchelon.NormalDemand in
lemma q46_negPart (m b y : ℝ) (hb : 0 < b) :
    ∫ t, max (t - y) 0 ∂(InventoryControl.newsboyDemand m b)
      = b * Theta ((y - m) / b) + (m - y) := by
  have hid : Integrable (fun t : ℝ => t) (InventoryControl.newsboyDemand m b) := by
    rw [InventoryControl.newsboyDemand_eq]
    exact (memLp_id_gaussianReal 1).integrable le_rfl
  have h2 : Integrable (fun t : ℝ => t - y) (InventoryControl.newsboyDemand m b) :=
    hid.sub (integrable_const y)
  have h1 : Integrable (fun t : ℝ => max (y - t) 0) (InventoryControl.newsboyDemand m b) :=
    ((integrable_const y).sub hid).pos_part
  have hf : (fun t : ℝ => max (t - y) 0) = fun t => max (y - t) 0 + (t - y) := by
    funext t
    rcases le_total t y with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  rw [hf, integral_add h1 h2, q46_posTheta m b y hb, integral_sub hid (integrable_const y)]
  rw [InventoryControl.newsboyDemand_eq, integral_id_gaussianReal]
  simp

open FZEchelon.NormalDemand in
lemma q46_R (D : Data) (hb : 0 < D.sd (D.l + 1)) (y : ℝ) :
    D.R y = -D.hd * (y - D.mean D.l)
      + D.pr * (D.sd (D.l + 1) * Theta ((y - D.mean (D.l + 1)) / D.sd (D.l + 1))
          + (D.mean (D.l + 1) - y))
      + (D.hd + D.hr) * (D.sd (D.l + 1) * Theta ((y - D.mean (D.l + 1)) / D.sd (D.l + 1))) := by
  unfold Data.R Data.law
  rw [q46_negPart _ _ _ hb, q46_posTheta _ _ _ hb]

lemma q46_lin5 (s : Set ℝ) (f1 f2 f3 f4 f5 : ℝ → ℝ) (h1 : Integrable f1) (h2 : Integrable f2)
    (h3 : Integrable f3) (h4 : Integrable f4) (h5 : Integrable f5) (A1 A2 A3 A4 A5 : ℝ) :
    ∫ z in s, (A1 * f1 z + A2 * f2 z + A3 * f3 z + A4 * f4 z + A5 * f5 z)
      = A1 * (∫ z in s, f1 z) + A2 * (∫ z in s, f2 z) + A3 * (∫ z in s, f3 z)
        + A4 * (∫ z in s, f4 z) + A5 * (∫ z in s, f5 z) := by
  have e1 := (h1.const_mul A1).integrableOn (s := s)
  have e2 := (h2.const_mul A2).integrableOn (s := s)
  have e3 := (h3.const_mul A3).integrableOn (s := s)
  have e4 := (h4.const_mul A4).integrableOn (s := s)
  have e5 := (h5.const_mul A5).integrableOn (s := s)
  rw [integral_add, integral_add, integral_add, integral_add]
  · simp only [integral_const_mul]
  all_goals first
    | exact e1 | exact e2 | exact e3 | exact e4 | exact e5
    | exact e1.add e2 | exact (e1.add e2).add e3 | exact ((e1.add e2).add e3).add e4

open FZEchelon.NormalDemand Data in
theorem solution (D : Data) (hσ : 0 < D.σ) (hhd : 0 < D.hd) (hhr : 0 < D.hr) (hpr : 0 < D.pr)
    (hL : 1 ≤ D.L) (hx : ∀ x, D.R D.xstar ≤ D.R x) :
    ∀ x : ℝ, D.PL x = D.ps * D.iota x - (D.ps + D.hr) * D.kappa x := by
  intro x
  -- basic positivity and the variance identity
  have hsd : ∀ i : ℕ, 1 ≤ i → 0 < D.sd i := by
    intro i hi
    unfold Data.sd
    have : (0 : ℝ) < i := by exact_mod_cast hi
    positivity
  have hsd2 : ∀ i : ℕ, D.sd i ^ 2 = (i : ℝ) * D.σ ^ 2 := by
    intro i
    unfold Data.sd
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg i)]
  set a := D.sd D.L with ha_def
  set b := D.sd (D.l + 1) with hb_def
  set c := D.sd (D.L + D.l + 1) with hc_def
  have ha : 0 < a := hsd _ hL
  have hb : 0 < b := hsd _ (by omega)
  have hc : 0 < c := hsd _ (by omega)
  have hc2 : c ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hc_def, ha_def, hb_def, hsd2, hsd2, hsd2]; push_cast; ring
  set mL := D.mean D.L with hmL
  set m1 := D.mean (D.l + 1) with hm1
  have hmT : D.mean (D.L + D.l + 1) = mL + m1 := by
    rw [hmL, hm1]; unfold Data.mean; push_cast; ring
  set xs := D.xstar with hxs
  set τ1 := D.tau1 x with hτ1
  set α := (x - mL - m1) / b with hα
  set β := a / b with hβ
  set γ := c / b with hγ
  have hβpos : 0 < β := div_pos ha hb
  have hγpos : 0 < γ := div_pos hc hb
  have hγ2 : γ ^ 2 = 1 + β ^ 2 := by
    rw [hγ, hβ, div_pow, div_pow, hc2]; field_simp; ring
  have hbβ : b * β = a := by rw [hβ]; field_simp
  have haτ : a * τ1 = xs + mL - x := by
    rw [hτ1]; unfold Data.tau1; rw [← ha_def, ← hmL, ← hxs]; field_simp; ring
  set ps := D.ps with hps
  set hr := D.hr with hhr_def
  set ν := D.nustar with hν
  have hνdef : ν = (xs - m1) / b := rfl
  -- Step A/B: rewrite PL as a set integral of an explicit integrand
  obtain ⟨E, hE⟩ : ∃ E : ℝ → ℝ, E = fun z =>
    ps * a * ((τ1 - z) * stdNormalPDF z)
    + (ps + hr) * (b * α) * (stdNormalCDF (α + β * z) * stdNormalPDF z)
    + (ps + hr) * a * ((z * stdNormalCDF (α + β * z) - β * stdNormalPDF (α + β * z)) * stdNormalPDF z)
    + (ps + hr) * (a * β + b) * (stdNormalPDF (α + β * z) * stdNormalPDF z)
    + (-((ps + hr) * (b * Theta ν))) * stdNormalPDF z := ⟨_, rfl⟩
  have hpt : ∀ z, stdNormalPDF z * D.P (x - (mL - a * z)) = (Set.Iio τ1).indicator E z := by
    intro z
    unfold Data.P
    rw [← hxs]
    by_cases hz : xs ≤ x - (mL - a * z)
    · rw [if_pos hz, mul_zero, Set.indicator_of_notMem]
      simp only [Set.mem_Iio, not_lt]
      exact le_of_mul_le_mul_left (by linarith) ha
    · rw [if_neg hz, Set.indicator_of_mem (show z ∈ Set.Iio τ1 by
        simp only [Set.mem_Iio]; exact lt_of_mul_lt_mul_left (by linarith) ha.le)]
      rw [q46_R D hb, q46_R D hb, ← hb_def, ← hm1]
      have hy : (x - (mL - a * z) - m1) / b = α + β * z := by
        rw [hα, hβ]; field_simp; ring
      rw [hy, ← hνdef]
      rw [hE]
      simp only [Theta]
      unfold Data.ps at hps
      rw [hps]
      linear_combination (-((D.hd + D.pr) * stdNormalPDF z)) * haτ
        + ((D.hd + D.pr + hr) * z * stdNormalCDF (α + β * z) * stdNormalPDF z) * hbβ
  have hPL : D.PL x = ∫ z in Set.Iic τ1, E z := by
    have h1 : D.PL x = ∫ z, stdNormalPDF z * D.P (x - (mL - a * z)) :=
      q46_gsub' mL a ha (fun t => D.P (x - t))
    rw [h1, integral_congr_ae (ae_of_all _ hpt), integral_indicator measurableSet_Iio,
      integral_Iic_eq_integral_Iio]
  rw [hPL, hE]
  rw [q46_lin5 _ _ _ _ _ _ (q46_i1 τ1) (q46_i2 α β) (q46_i3 α β) (q46_i4 α β) q46_int_pdf]
  rw [q46_L1, q46_L2 α β τ1 hβpos, q46_L3 α β γ τ1 hγpos hγ2, q46_int_cdf]
  -- the bivariate term
  have hρk : (b / c) ^ 2 = 1 - D.rho ^ 2 := by
    unfold Data.rho; rw [← ha_def, ← hc_def, div_pow, neg_sq, div_pow]
    field_simp; linarith
  have hG : ∫ z in Set.Iic τ1, stdNormalCDF (α + β * z) * stdNormalPDF z
      = bivNormalCDF τ1 (D.tau2 x) D.rho := by
    unfold bivNormalCDF
    refine setIntegral_congr_fun measurableSet_Iic (fun s _ => ?_)
    rw [q46_inner D.rho (b / c) s _ (div_pos hb hc) hρk, mul_comm]
    congr 1
    unfold Data.tau2 Data.rho
    rw [← ha_def, ← hc_def, hmT, hα, hβ]
    field_simp
    ring
  rw [hG]
  -- the remaining closed-form identities
  have h1 : α + β * τ1 = ν := by
    rw [hνdef, hα, hβ]
    have : a * τ1 = xs + mL - x := haτ
    field_simp
    linear_combination this
  have h2 : α / γ = D.tau2 x := by
    unfold Data.tau2; rw [← hc_def, hmT, hα, hγ]; field_simp; ring
  have h3 : γ * τ1 + α * β / γ = D.tau3 x := by
    unfold Data.tau3
    rw [← ha_def, ← hb_def, ← hc_def, ← hmL, ← hm1, ← hxs, hγ, hα, hβ]
    have : a * τ1 = xs + mL - x := haτ
    field_simp
    linear_combination c ^ 2 * this - (x - mL - xs) * hc2
  rw [h1, h2, h3]
  have hcoef : (a * β + b) / γ = c := by
    rw [div_eq_iff hγpos.ne', hβ, hγ]
    calc a * (a / b) + b = (a ^ 2 + b ^ 2) / b := by field_simp
      _ = c * (c / b) := by rw [← hc2]; ring
  unfold Data.iota Data.kappa Data.eps1 Data.eps2
  rw [← ha_def, ← hb_def, ← hc_def, hmT, ← hτ1, ← hν]
  have hbα : b * α = x - (mL + m1) := by rw [hα]; field_simp; ring
  have hk1 : (a * β + b) * (stdNormalPDF (D.tau2 x) * (stdNormalCDF (D.tau3 x) / γ))
      = c * (stdNormalCDF (D.tau3 x) * stdNormalPDF (D.tau2 x)) := by
    rw [← hcoef]; field_simp
  have hk2 : c ^ 2 * (stdNormalCDF (D.tau3 x) * stdNormalPDF (D.tau2 x) / c)
      = c * (stdNormalCDF (D.tau3 x) * stdNormalPDF (D.tau2 x)) := by
    field_simp
  have hk3 : a ^ 2 * (stdNormalCDF ν * stdNormalPDF τ1 / a) = a * (stdNormalCDF ν * stdNormalPDF τ1) := by
    field_simp
  linear_combination (ps + hr) * hk1 - (ps + hr) * hk2 + (ps + hr) * hk3
    + (ps + hr) * bivNormalCDF τ1 (D.tau2 x) D.rho * hbα
