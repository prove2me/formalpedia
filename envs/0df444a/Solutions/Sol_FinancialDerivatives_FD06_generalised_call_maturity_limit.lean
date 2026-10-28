-- Prove2me | solution 1 for FinancialDerivatives.FD06.generalised_call_maturity_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:24:36.590055+00:00
-- url     : https://prove2.me/submissions/e5d5c6bb-97bd-49b0-8558-6553d467582d

import Mathlib
import Definitions.Def_fd06_generalisedCall
import Definitions.Def_fd06_generalisedPut
import Definitions.Def_fd06_standardNormalDensity
import Definitions.Def_fd06_standardNormalCDF
import Definitions.Def_fd06_generalisedD1
import Definitions.Def_fd06_generalisedD2
open FinancialDerivatives.FD06 MeasureTheory ProbabilityTheory

lemma H_mat_pdf_eq (x : ℝ) : gaussianPDFReal 0 1 x = standardNormalDensity x := by
  simp [gaussianPDFReal, standardNormalDensity, div_eq_inv_mul]

lemma H_mat_dens_cont : Continuous standardNormalDensity := by
  unfold standardNormalDensity; fun_prop

lemma H_mat_dens_int : Integrable standardNormalDensity := by
  have : standardNormalDensity = gaussianPDFReal 0 1 := funext fun x => (H_mat_pdf_eq x).symm
  rw [this]; exact integrable_gaussianPDFReal 0 1

lemma H_mat_cdf_eq (x : ℝ) : standardNormalCDF x = ∫ t in Set.Iic x, standardNormalDensity t := by
  unfold standardNormalCDF
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
      (fun t _ => gaussianPDFReal_nonneg _ _ t))]
  simp_rw [H_mat_pdf_eq]

lemma H_mat_cdf_sub (x : ℝ) :
    standardNormalCDF x = standardNormalCDF 0 + ∫ t in (0:ℝ)..x, standardNormalDensity t := by
  rw [H_mat_cdf_eq, H_mat_cdf_eq, ← intervalIntegral.integral_Iic_sub_Iic
    H_mat_dens_int.integrableOn H_mat_dens_int.integrableOn]
  ring

lemma H_mat_cdf_hasDerivAt (x : ℝ) :
    HasDerivAt standardNormalCDF (standardNormalDensity x) x := by
  have h : standardNormalCDF = fun y => standardNormalCDF 0 + ∫ t in (0:ℝ)..y, standardNormalDensity t :=
    funext H_mat_cdf_sub
  rw [h]
  exact ((H_mat_dens_cont.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _

lemma H_mat_cdf_cont : Continuous standardNormalCDF :=
  continuous_iff_continuousAt.2 fun x => (H_mat_cdf_hasDerivAt x).continuousAt

lemma H_mat_key (s k R Q V : ℝ) (hs : 0 < s) (hk : 0 < k) (hV : 0 < V) :
    s * Real.exp (-Q) * standardNormalDensity (generalisedD1 s k R Q V)
      = k * Real.exp (-R) * standardNormalDensity (generalisedD2 s k R Q V) := by
  unfold standardNormalDensity generalisedD2
  set d := generalisedD1 s k R Q V with hd
  have hsq : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have h1 : d * Real.sqrt V = Real.log (s / k) + R - Q + V / 2 := by
    rw [hd, generalisedD1, div_mul_cancel₀ _ hsq.ne']
  have h2 : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV.le
  have e : Real.log (s / k) + -Q + -d ^ 2 / 2 = -R + -(d - Real.sqrt V) ^ 2 / 2 := by
    linear_combination (-1) * h1 + (1/2) * h2
  rw [← mul_div_assoc, ← mul_div_assoc]
  congr 1
  calc s * Real.exp (-Q) * Real.exp (-d ^ 2 / 2)
      = k * Real.exp (Real.log (s / k) + -Q + -d ^ 2 / 2) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hs hk)]; field_simp
    _ = k * Real.exp (-R + -(d - Real.sqrt V) ^ 2 / 2) := by rw [e]
    _ = _ := by rw [Real.exp_add]; ring

/-- master chain rule -/
lemma H_mat_call_hasDerivAt (s k R Q V : ℝ → ℝ) (u s' k' R' Q' V' : ℝ)
    (hs : HasDerivAt s s' u) (hk : HasDerivAt k k' u) (hR : HasDerivAt R R' u)
    (hQ : HasDerivAt Q Q' u) (hV : HasDerivAt V V' u)
    (hs0 : 0 < s u) (hk0 : 0 < k u) (hV0 : 0 < V u) :
    HasDerivAt (fun x => generalisedCall (s x) (k x) (R x) (Q x) (V x))
      (Real.exp (-Q u) * standardNormalCDF (generalisedD1 (s u) (k u) (R u) (Q u) (V u)) * s'
       - Real.exp (-R u) * standardNormalCDF (generalisedD2 (s u) (k u) (R u) (Q u) (V u)) * k'
       + k u * Real.exp (-R u) * standardNormalCDF (generalisedD2 (s u) (k u) (R u) (Q u) (V u)) * R'
       - s u * Real.exp (-Q u) * standardNormalCDF (generalisedD1 (s u) (k u) (R u) (Q u) (V u)) * Q'
       + s u * Real.exp (-Q u) * standardNormalDensity (generalisedD1 (s u) (k u) (R u) (Q u) (V u))
          * V' / (2 * Real.sqrt (V u))) u := by
  have hsq : 0 < Real.sqrt (V u) := Real.sqrt_pos.2 hV0
  have hsqd : HasDerivAt (fun x => Real.sqrt (V x)) (V' / (2 * Real.sqrt (V u))) u :=
    hV.sqrt hV0.ne'
  have hlog : HasDerivAt (fun x => Real.log (s x / k x)) ((s' * k u - s u * k') / k u ^ 2 / (s u / k u)) u :=
    (hs.div hk hk0.ne').log (div_pos hs0 hk0).ne'
  have hnum := ((hlog.add hR).sub hQ).add (hV.div_const 2)
  have hd1 : HasDerivAt (fun x => generalisedD1 (s x) (k x) (R x) (Q x) (V x)) _ u :=
    hnum.div hsqd hsq.ne'
  have hd2 : HasDerivAt (fun x => generalisedD2 (s x) (k x) (R x) (Q x) (V x)) _ u :=
    hd1.sub hsqd
  have hN1 := (H_mat_cdf_hasDerivAt (generalisedD1 (s u) (k u) (R u) (Q u) (V u))).comp u hd1
  have hN2 := (H_mat_cdf_hasDerivAt (generalisedD2 (s u) (k u) (R u) (Q u) (V u))).comp u hd2
  have hE1 : HasDerivAt (fun x => Real.exp (-Q x)) (Real.exp (-Q u) * -Q') u := hQ.neg.exp
  have hE2 : HasDerivAt (fun x => Real.exp (-R x)) (Real.exp (-R u) * -R') u := hR.neg.exp
  have hC := ((hs.mul hE1).mul hN1).sub ((hk.mul hE2).mul hN2)
  unfold generalisedCall
  refine hC.congr_deriv ?_
  have key := H_mat_key (s u) (k u) (R u) (Q u) (V u) hs0 hk0 hV0
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Function.comp_apply]
  set X := ((s' * k u - s u * k') / k u ^ 2 / (s u / k u) + R' - Q' + V' / 2) * Real.sqrt (V u) -
          (Real.log (s u / k u) + R u - Q u + V u / 2) * (V' / (2 * Real.sqrt (V u)))
  linear_combination (X / Real.sqrt (V u) ^ 2 - V' / (2 * Real.sqrt (V u))) * key

open Filter Topology

lemma H_mat_delta_hasDerivAt (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) :
    HasDerivAt (fun x => generalisedCall x K R Q V)
      (Real.exp (-Q) * standardNormalCDF (generalisedD1 S K R Q V)) S := by
  have h := H_mat_call_hasDerivAt (fun x => x) (fun _ => K) (fun _ => R) (fun _ => Q) (fun _ => V)
    S 1 0 0 0 0 (hasDerivAt_id' S) (hasDerivAt_const _ _) (hasDerivAt_const _ _)
    (hasDerivAt_const _ _) (hasDerivAt_const _ _) hS hK hV
  refine h.congr_deriv ?_
  simp

lemma H_mat_gamma_aux (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) :
    HasDerivAt (fun x => Real.exp (-Q) * standardNormalCDF (generalisedD1 x K R Q V))
      (Real.exp (-Q) * standardNormalDensity (generalisedD1 S K R Q V) / (S * Real.sqrt V)) S := by
  have hsq := Real.sqrt_pos.2 hV
  have hd1 : HasDerivAt (fun x => generalisedD1 x K R Q V) ((1 / K) / (S / K) / Real.sqrt V) S := by
    have := (((((hasDerivAt_id' S).div_const K).log (div_pos hS hK).ne').add_const R).sub_const Q
      |>.add_const (V / 2)).div_const (Real.sqrt V)
    exact this
  have := ((H_mat_cdf_hasDerivAt (generalisedD1 S K R Q V)).comp S hd1).const_mul (Real.exp (-Q))
  refine this.congr_deriv ?_
  field_simp

lemma H_mat_gamma (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) :
    deriv (deriv (fun x => generalisedCall x K R Q V)) S
      = Real.exp (-Q) * standardNormalDensity (generalisedD1 S K R Q V) / (S * Real.sqrt V) := by
  have hev : deriv (fun x => generalisedCall x K R Q V) =ᶠ[𝓝 S]
      fun x => Real.exp (-Q) * standardNormalCDF (generalisedD1 x K R Q V) := by
    filter_upwards [Ioi_mem_nhds hS] with x hx
    exact (H_mat_delta_hasDerivAt x K R Q V hx hK hV).deriv
  rw [hev.deriv_eq, (H_mat_gamma_aux S K R Q V hS hK hV).deriv]

lemma H_mat_vega_hasDerivAt (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) :
    HasDerivAt (fun v => generalisedCall S K R Q v)
      (S * Real.exp (-Q) * standardNormalDensity (generalisedD1 S K R Q V) / (2 * Real.sqrt V)) V := by
  have h := H_mat_call_hasDerivAt (fun _ => S) (fun _ => K) (fun _ => R) (fun _ => Q) (fun x => x)
    V 0 0 0 0 1 (hasDerivAt_const _ _) (hasDerivAt_const _ _) (hasDerivAt_const _ _)
    (hasDerivAt_const _ _) (hasDerivAt_id' V) hS hK hV
  refine h.congr_deriv ?_
  simp

lemma H_mat_strike_hasDerivAt (S K R Q V : ℝ) (hS : 0 < S) (hK : 0 < K) (hV : 0 < V) :
    HasDerivAt (fun k => generalisedCall S k R Q V)
      (-(Real.exp (-R) * standardNormalCDF (generalisedD2 S K R Q V))) K := by
  have h := H_mat_call_hasDerivAt (fun _ => S) (fun x => x) (fun _ => R) (fun _ => Q) (fun _ => V)
    K 0 1 0 0 0 (hasDerivAt_const _ _) (hasDerivAt_id' K) (hasDerivAt_const _ _)
    (hasDerivAt_const _ _) (hasDerivAt_const _ _) hS hK hV
  refine h.congr_deriv ?_
  simp

lemma H_mat_cdf_neg (x : ℝ) : standardNormalCDF (-x) = 1 - standardNormalCDF x := by
  let g := fun y => standardNormalCDF (-y) + standardNormalCDF y
  have hg : ∀ y, HasDerivAt g 0 y := by
    intro y
    have h1 := (H_mat_cdf_hasDerivAt (-y)).comp y (hasDerivAt_neg y)
    have h2 := h1.add (H_mat_cdf_hasDerivAt y)
    refine h2.congr_deriv ?_
    simp [standardNormalDensity]
  have hc : ∀ y, g y = g 0 := fun y =>
    is_const_of_deriv_eq_zero (fun z => (hg z).differentiableAt) (fun z => (hg z).deriv) y 0
  have hlim : Tendsto g atTop (𝓝 (0 + 1)) :=
    ((ProbabilityTheory.tendsto_cdf_atBot _).comp tendsto_neg_atTop_atBot).add
      (ProbabilityTheory.tendsto_cdf_atTop _)
  have hlim2 : Tendsto g atTop (𝓝 (g 0)) := by
    have : g = fun _ => g 0 := funext hc
    rw [this]; exact tendsto_const_nhds
  have h0 := tendsto_nhds_unique hlim2 hlim
  have hx := hc x
  simp only [g] at hx h0
  linarith

lemma H_mat_put_eq (s k R Q V : ℝ) : generalisedPut s k R Q V
    = generalisedCall s k R Q V - s * Real.exp (-Q) + k * Real.exp (-R) := by
  unfold generalisedPut generalisedCall
  rw [H_mat_cdf_neg, H_mat_cdf_neg]
  ring

lemma H_mat_int_left (g : ℝ → ℝ) (hg : Continuous g) (t T : ℝ) :
    HasDerivAt (fun u => ∫ x in u..T, g x) (-g t) t := by
  have h : (fun u => ∫ x in u..T, g x) = fun u => -∫ x in T..u, g x := by
    funext u; rw [intervalIntegral.integral_symm]
  rw [h]
  exact (hg.integral_hasStrictDerivAt T t).hasDerivAt.neg


lemma H_mat_sqrt_tendsto : Tendsto (fun V : ℝ => Real.sqrt V) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := Real.continuous_sqrt.tendsto 0
    rw [Real.sqrt_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with V hV
    exact Real.sqrt_pos.2 hV

lemma H_mat_sqrt_tendsto0 : Tendsto (fun V : ℝ => Real.sqrt V / 2) (𝓝[>] 0) (𝓝 0) := by
  have := (H_mat_sqrt_tendsto.mono_right nhdsWithin_le_nhds).div_const 2
  simpa using this

lemma H_mat_d1_eq (S K V : ℝ) (hV : 0 < V) :
    generalisedD1 S K 0 0 V = Real.log (S / K) * (Real.sqrt V)⁻¹ + Real.sqrt V / 2 := by
  have h2 := Real.sq_sqrt hV.le
  have hs := (Real.sqrt_pos.2 hV).ne'
  rw [generalisedD1]
  field_simp
  linarith [h2]

lemma H_mat_d2_eq (S K V : ℝ) (hV : 0 < V) :
    generalisedD2 S K 0 0 V = Real.log (S / K) * (Real.sqrt V)⁻¹ + -(Real.sqrt V / 2) := by
  rw [generalisedD2, H_mat_d1_eq S K V hV]; ring

theorem solution (S K : ℝ) (hS : 0 < S) (hK : 0 < K) : Filter.Tendsto (fun V : ℝ => generalisedCall S K 0 0 V) (nhdsWithin 0 (Set.Ioi 0)) (nhds (max (S - K) 0)) := by
  have hev1 : (fun V => Real.log (S / K) * (Real.sqrt V)⁻¹ + Real.sqrt V / 2)
      =ᶠ[𝓝[>] (0:ℝ)] fun V => generalisedD1 S K 0 0 V := by
    filter_upwards [self_mem_nhdsWithin] with V hV
    exact (H_mat_d1_eq S K V hV).symm
  have hev2 : (fun V => Real.log (S / K) * (Real.sqrt V)⁻¹ + -(Real.sqrt V / 2))
      =ᶠ[𝓝[>] (0:ℝ)] fun V => generalisedD2 S K 0 0 V := by
    filter_upwards [self_mem_nhdsWithin] with V hV
    exact (H_mat_d2_eq S K V hV).symm
  have hinv := tendsto_inv_nhdsGT_zero.comp H_mat_sqrt_tendsto
  have hneg : Tendsto (fun V : ℝ => -(Real.sqrt V / 2)) (𝓝[>] 0) (𝓝 0) := by
    simpa using H_mat_sqrt_tendsto0.neg
  have hC : (fun V : ℝ => generalisedCall S K 0 0 V) = fun V =>
      S * standardNormalCDF (generalisedD1 S K 0 0 V) - K * standardNormalCDF (generalisedD2 S K 0 0 V) := by
    funext V; simp [generalisedCall]
  rw [hC]
  rcases lt_trichotomy K S with h | h | h
  · have hL : 0 < Real.log (S / K) := Real.log_pos ((one_lt_div hK).2 h)
    have h1 : Tendsto (fun V => generalisedD1 S K 0 0 V) (𝓝[>] 0) atTop :=
      ((Tendsto.const_mul_atTop hL hinv).atTop_add H_mat_sqrt_tendsto0).congr' hev1
    have h2 : Tendsto (fun V => generalisedD2 S K 0 0 V) (𝓝[>] 0) atTop :=
      ((Tendsto.const_mul_atTop hL hinv).atTop_add hneg).congr' hev2
    have := ((tendsto_cdf_atTop (μ := ProbabilityTheory.gaussianReal 0 1)).comp h1).const_mul S |>.sub
      (((tendsto_cdf_atTop (μ := ProbabilityTheory.gaussianReal 0 1)).comp h2).const_mul K)
    rw [max_eq_left (by linarith)]
    simpa [standardNormalCDF, Function.comp_def] using this
  · subst h
    have h1 : Tendsto (fun V => generalisedD1 K K 0 0 V) (𝓝[>] 0) (𝓝 0) := by
      refine Tendsto.congr' hev1 ?_
      simpa using H_mat_sqrt_tendsto0
    have h2 : Tendsto (fun V => generalisedD2 K K 0 0 V) (𝓝[>] 0) (𝓝 0) := by
      refine Tendsto.congr' hev2 ?_
      simpa using hneg
    have := (((H_mat_cdf_cont.tendsto 0).comp h1).const_mul K).sub (((H_mat_cdf_cont.tendsto 0).comp h2).const_mul K)
    simpa [Function.comp_def] using this
  · have hL : Real.log (S / K) < 0 := Real.log_neg (div_pos hS hK) ((div_lt_one hK).2 h)
    have h1 : Tendsto (fun V => generalisedD1 S K 0 0 V) (𝓝[>] 0) atBot :=
      ((Tendsto.const_mul_atTop_of_neg hL hinv).atBot_add H_mat_sqrt_tendsto0).congr' hev1
    have h2 : Tendsto (fun V => generalisedD2 S K 0 0 V) (𝓝[>] 0) atBot :=
      ((Tendsto.const_mul_atTop_of_neg hL hinv).atBot_add hneg).congr' hev2
    have := ((tendsto_cdf_atBot (μ := ProbabilityTheory.gaussianReal 0 1)).comp h1).const_mul S |>.sub
      (((tendsto_cdf_atBot (μ := ProbabilityTheory.gaussianReal 0 1)).comp h2).const_mul K)
    rw [max_eq_right (by linarith)]
    simpa [standardNormalCDF, Function.comp_def] using this
