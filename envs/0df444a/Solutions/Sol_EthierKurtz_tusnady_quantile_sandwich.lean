-- Prove2me | solution 1 for EthierKurtz.tusnady_quantile_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T01:05:09.89132+00:00
-- url     : https://prove2.me/submissions/f7a9352a-37a0-453b-8200-5f2d920a4614

import Mathlib.Tactic
import Mathlib




open MeasureTheory Set ProbabilityTheory

namespace TusAux

local notation "Ncdf" => ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))

noncomputable def T (r : ℝ) : ℝ := ∫ t in Set.Ioi r, Real.exp (-t^2/2)

lemma integrable_E : Integrable (fun t : ℝ => Real.exp (-t^2/2)) := by
  have := integrable_exp_neg_mul_sq (b := 1/2) (by norm_num)
  refine this.congr (ae_of_all _ fun t => ?_)
  simp only; congr 1; ring

lemma gauss_real_eq (S : Set ℝ) (hS : MeasurableSet S) :
    (gaussianReal 0 1).real S = ∫ t in S, gaussianPDFReal 0 1 t := by
  rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg hS fun _ _ => gaussianPDFReal_nonneg _ _ _)]

lemma psi_eq_int (r : ℝ) : 1 - Ncdf r = ∫ t in Ioi r, gaussianPDFReal 0 1 t := by
  rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Iic, compl_Iic,
    gauss_real_eq _ measurableSet_Ioi]

lemma psi_eq (r : ℝ) : 1 - Ncdf r = (√(2 * Real.pi))⁻¹ * T r := by
  rw [psi_eq_int]
  unfold T
  rw [← integral_const_mul]
  congr 1; ext t
  simp [gaussianPDFReal]

lemma phi_neg (x : ℝ) : Ncdf (-x) = 1 - Ncdf x := by
  rw [psi_eq_int, cdf_eq_real, gauss_real_eq _ measurableSet_Iic, ← integral_comp_neg_Ioi]
  congr 1; ext t
  simp [gaussianPDFReal]

lemma psi_nonneg (r : ℝ) : 0 ≤ 1 - Ncdf r := sub_nonneg.2 (cdf_le_one _ _)

lemma shift_Ioi (f : ℝ → ℝ) (a d : ℝ) :
    ∫ t in Ioi (a + d), f t = ∫ t in Ioi a, f (t + d) := by
  have A : MeasurableEmbedding fun x : ℝ => x + d :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have := MeasurableEmbedding.setIntegral_map (μ := volume) A f (Ioi (a + d))
  rw [map_add_right_eq_self] at this
  rw [this, preimage_add_const_Ioi, add_sub_cancel_right]

lemma T_shift {a d : ℝ} (_ha : 0 ≤ a) (hd : 0 ≤ d) :
    T (a + d) ≤ Real.exp (-(a * d)) * T a := by
  unfold T
  rw [shift_Ioi (fun t => Real.exp (-t^2/2)), ← integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi ?_
  · exact (integrable_E.comp_add_right d).integrableOn
  · exact (integrable_E.const_mul _).integrableOn
  · intro t ht
    have ht' : a < t := ht
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg hd (sub_nonneg.2 ht'.le), mul_nonneg hd _ha]

lemma psi_shift {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) :
    1 - Ncdf (a + d) ≤ (1 - Ncdf a) * Real.exp (-(a * d)) := by
  rw [psi_eq, psi_eq]
  have hs : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
  calc (√(2 * Real.pi))⁻¹ * T (a + d) ≤ (√(2 * Real.pi))⁻¹ * (Real.exp (-(a * d)) * T a) :=
        mul_le_mul_of_nonneg_left (T_shift ha hd) hs
    _ = _ := by ring

lemma T_sub {a b : ℝ} : T a - T b = ∫ t in a..b, Real.exp (-t^2/2) := by
  unfold T
  exact intervalIntegral.integral_Ioi_sub_Ioi' integrable_E.integrableOn integrable_E.integrableOn

lemma gauss_incr {a b : ℝ} (ha : -3 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    (√(2 * Real.pi))⁻¹ * Real.exp (-9/2) * (b - a) ≤ Ncdf b - Ncdf a := by
  have e : Ncdf b - Ncdf a = (1 - Ncdf a) - (1 - Ncdf b) := by ring
  rw [e, psi_eq, psi_eq, ← mul_sub, T_sub, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h1 : ∫ t in a..b, Real.exp (-9/2 : ℝ) = (b - a) * Real.exp (-9/2) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  rw [mul_comm, ← h1]
  apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t^2/2)).intervalIntegrable _ _)
  intro t ht
  apply Real.exp_le_exp.2
  have : t^2 ≤ 9 := by nlinarith [ht.1, ht.2]
  linarith

lemma upper_core {s cR A y u : ℝ} (hs : 0 < s) (hy : 0 ≤ y) (hyu : y ≤ u) (hu2 : u ≤ 2 * y)
    (hcR : 0 ≤ cR) (hA : 8 * cR ≤ A) (hd : A * (y^2 / s^2) ≤ u - y) :
    (1 - Ncdf (u / s)) * Real.exp (cR * (u^3 / (s^2)^2)) ≤ 1 - Ncdf (y / s) := by
  have h1 := psi_shift (div_nonneg hy hs.le) (div_nonneg (sub_nonneg.2 hyu) hs.le)
  rw [show y / s + (u - y) / s = u / s by field_simp; ring] at h1
  have hu3 : u^3 ≤ 8 * y^3 := by
    calc u^3 ≤ (2 * y)^3 := pow_le_pow_left₀ (hy.trans hyu) hu2 3
      _ = 8 * y^3 := by ring
  have hP : 0 ≤ y^3 / (s^2)^2 := by positivity
  have hkey : cR * (u^3 / (s^2)^2) ≤ y / s * ((u - y) / s) := by
    have e1 : y / s * ((u - y) / s) = y * (u - y) / s^2 := by rw [div_mul_div_comm, sq]
    have e2 : y * (A * (y^2 / s^2)) / s^2 = A * (y^3 / (s^2)^2) := by field_simp
    have h2 : y * (A * (y^2 / s^2)) ≤ y * (u - y) := mul_le_mul_of_nonneg_left hd hy
    have h3 : y * (A * (y^2 / s^2)) / s^2 ≤ y * (u - y) / s^2 :=
      div_le_div_of_nonneg_right h2 (by positivity)
    have h4 : cR * (u^3 / (s^2)^2) ≤ cR * (8 * y^3 / (s^2)^2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hu3 (by positivity)) hcR
    have h5 : cR * (8 * y^3 / (s^2)^2) = 8 * cR * (y^3 / (s^2)^2) := by ring
    have h6 : 8 * cR * (y^3 / (s^2)^2) ≤ A * (y^3 / (s^2)^2) :=
      mul_le_mul_of_nonneg_right hA hP
    rw [e1]; linarith
  calc (1 - Ncdf (u / s)) * Real.exp (cR * (u^3 / (s^2)^2))
      ≤ (1 - Ncdf (y / s)) * Real.exp (-(y / s * ((u - y) / s))) *
          Real.exp (cR * (u^3 / (s^2)^2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (1 - Ncdf (y / s)) * Real.exp (cR * (u^3 / (s^2)^2) - y / s * ((u - y) / s)) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_eq_sub]
    _ ≤ (1 - Ncdf (y / s)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by linarith)) (psi_nonneg _)
    _ = _ := mul_one _

lemma lower_core {s cR A y v : ℝ} (hs : 0 < s) (hv0 : 0 ≤ v) (hyv : y / 2 ≤ v) (hvy : v ≤ y)
    (hcR : 0 ≤ cR) (hA : 2 * cR ≤ A) (hd : A * (y^2 / s^2) ≤ y - v) :
    1 - Ncdf (y / s) ≤ (1 - Ncdf (v / s)) * Real.exp (-(cR * (v^3 / (s^2)^2))) := by
  have hy : 0 ≤ y := hv0.trans hvy
  have h1 := psi_shift (div_nonneg hv0 hs.le) (div_nonneg (sub_nonneg.2 hvy) hs.le)
  rw [show v / s + (y - v) / s = y / s by field_simp; ring] at h1
  have hv3 : v^3 ≤ y^3 := pow_le_pow_left₀ hv0 hvy 3
  have hP : 0 ≤ y^3 / (s^2)^2 := by positivity
  have hA0 : 0 ≤ A := by linarith
  have hkey : cR * (v^3 / (s^2)^2) ≤ v / s * ((y - v) / s) := by
    have e1 : v / s * ((y - v) / s) = v * (y - v) / s^2 := by rw [div_mul_div_comm, sq]
    have e2 : y / 2 * (A * (y^2 / s^2)) / s^2 = A / 2 * (y^3 / (s^2)^2) := by field_simp
    have h2 : y / 2 * (A * (y^2 / s^2)) ≤ v * (y - v) :=
      mul_le_mul hyv hd (by positivity) hv0
    have h3 : y / 2 * (A * (y^2 / s^2)) / s^2 ≤ v * (y - v) / s^2 :=
      div_le_div_of_nonneg_right h2 (by positivity)
    have h4 : cR * (v^3 / (s^2)^2) ≤ cR * (y^3 / (s^2)^2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hv3 (by positivity)) hcR
    have h6 : cR * (y^3 / (s^2)^2) ≤ A / 2 * (y^3 / (s^2)^2) :=
      mul_le_mul_of_nonneg_right (by linarith) hP
    rw [e1]; linarith
  calc 1 - Ncdf (y / s) ≤ (1 - Ncdf (v / s)) * Real.exp (-(v / s * ((y - v) / s))) := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (psi_nonneg _)

lemma cdf_eq_one_sub (L : Measure ℝ) [IsProbabilityMeasure L] (x : ℝ) :
    cdf L x = 1 - L.real (Ioi x) := by
  rw [cdf_eq_real, ← probReal_compl_eq_one_sub measurableSet_Ioi, compl_Ioi]

lemma cdf_ge_Iio (L : Measure ℝ) [IsProbabilityMeasure L] (x : ℝ) :
    L.real (Iio x) ≤ cdf L x := by
  rw [cdf_eq_real]; exact measureReal_mono Iio_subset_Iic_self

lemma cdf_le_Iio (L : Measure ℝ) [IsProbabilityMeasure L] {x x' : ℝ} (h : x < x') :
    cdf L x ≤ L.real (Iio x') := by
  rw [cdf_eq_real]; exact measureReal_mono (Iic_subset_Iio.2 h)

lemma caseA {s c K y : ℝ} (F : ℝ → ℝ) (hs : 0 < s) (hc : 0 < c) (hcs : 5 * c ≤ s)
    (hKc : K ≤ (√(2 * Real.pi))⁻¹ * Real.exp (-9/2) * c)
    (hBE : ∀ z : ℝ, |z| ≤ 3 → Ncdf z - K / s ≤ F (s * z) ∧ F (s * z) ≤ Ncdf z + K / s)
    (hy : |y| ≤ 2 * s) :
    Ncdf (y / s) ≤ F (y + c * (1 + y^2 / s^2)) ∧ F (y - c * (1 + y^2 / s^2)) ≤ Ncdf (y / s) := by
  set φ3 : ℝ := (√(2 * Real.pi))⁻¹ * Real.exp (-9/2) with hφ3
  have hφ : 0 < φ3 := by positivity
  have hp : y + c * (1 + y^2 / s^2) = s * (y / s + c * (1 + (y / s)^2) / s) := by
    field_simp
  have hm : y - c * (1 + y^2 / s^2) = s * (y / s - c * (1 + (y / s)^2) / s) := by
    field_simp
  have hz : |y / s| ≤ 2 := by rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]; linarith
  set z := y / s with hzdef
  have hz2 : z^2 ≤ 4 := by nlinarith [abs_nonneg z, sq_abs z]
  have hzb := abs_le.1 hz
  set d := c * (1 + z^2) / s with hddef
  have hds : d * s = c * (1 + z^2) := by rw [hddef]; field_simp
  have hd0 : 0 ≤ d := by positivity
  have hd1 : d ≤ 1 := by
    rw [hddef, div_le_one hs]; nlinarith
  have hKs : K / s ≤ φ3 * d := by
    rw [div_le_iff₀ hs]
    calc K ≤ φ3 * c := hKc
      _ ≤ φ3 * c * (1 + z^2) := le_mul_of_one_le_right (by positivity) (by nlinarith)
      _ = φ3 * (d * s) := by rw [hds]; ring
      _ = φ3 * d * s := by ring
  constructor
  · rw [hp]
    have h1 := (hBE (z + d) (abs_le.2 ⟨by linarith, by linarith⟩)).1
    have h2 := gauss_incr (a := z) (b := z + d) (by linarith) (by linarith) (by linarith)
    rw [← hφ3] at h2
    have : φ3 * (z + d - z) = φ3 * d := by ring
    linarith
  · rw [hm]
    have h1 := (hBE (z - d) (abs_le.2 ⟨by linarith, by linarith⟩)).2
    have h2 := gauss_incr (a := z - d) (b := z) (by linarith) (by linarith) (by linarith)
    rw [← hφ3] at h2
    have : φ3 * (z - (z - d)) = φ3 * d := by ring
    linarith

lemma delta_le {s c ε y : ℝ} (hs : 0 < s) (hc : 0 < c) (hcs : 5 * c ≤ s) (hcε : c * ε ≤ 1/4)
    (hy2 : 2 * s < y) (hyε : y ≤ ε * s^2) :
    c * (y^2 / s^2) ≤ c * (1 + y^2 / s^2) ∧ c * (1 + y^2 / s^2) ≤ y / 2 := by
  have hy0 : 0 < y := by linarith
  have h0 : y^2 / s^2 ≤ ε * y := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hyε hy0.le]
  have h1 : c * (y^2 / s^2) ≤ c * (ε * y) := mul_le_mul_of_nonneg_left h0 hc.le
  have h2 : c * (ε * y) ≤ y / 4 := by
    have := mul_le_mul_of_nonneg_right hcε hy0.le
    linarith [show c * (ε * y) = c * ε * y by ring]
  have e : c * (1 + y^2 / s^2) = c + c * (y^2 / s^2) := by ring
  constructor <;> linarith

lemma caseB {s c ε cR εR y : ℝ} (L : Measure ℝ) [IsProbabilityMeasure L] (hs : 0 < s)
    (hc : 0 < c) (hcs : 5 * c ≤ s) (hcε : c * ε ≤ 1/4) (hεR0 : 0 < εR) (hεR : ε ≤ εR / 2)
    (hcR : 0 < cR) (h16 : 16 * cR ≤ c)
    (hR : ∀ y : ℝ, s ≤ y → y ≤ εR * s^2 →
      L.real (Ioi y) ≤ (1 - Ncdf (y / s)) * Real.exp (cR * (y^3 / (s^2)^2)) ∧
      (1 - Ncdf (y / s)) * Real.exp (-(cR * (y^3 / (s^2)^2))) ≤ L.real (Ioi y))
    (hy2 : 2 * s < y) (hyε : y ≤ ε * s^2) :
    Ncdf (y / s) ≤ cdf L (y + c * (1 + y^2 / s^2)) ∧
      cdf L (y - c * (1 + y^2 / s^2)) ≤ Ncdf (y / s) := by
  obtain ⟨hδ1, hδ2⟩ := delta_le hs hc hcs hcε hy2 hyε
  set δ := c * (1 + y^2 / s^2)
  have hX : 0 ≤ c * (y^2 / s^2) := by positivity
  have hεs : ε * s^2 ≤ εR / 2 * s^2 := mul_le_mul_of_nonneg_right hεR (sq_nonneg s)
  have hεRs : 0 ≤ εR * s^2 := by positivity
  constructor
  · have hu := (hR (y + δ) (by linarith) (by linarith)).1
    have hc' := upper_core (cR := cR) (A := c) (y := y) (u := y + δ) hs (by linarith) (by linarith) (by linarith)
      hcR.le (by linarith) (by linarith)
    rw [cdf_eq_one_sub L]; linarith
  · have hv := (hR (y - δ) (by linarith) (by linarith)).2
    have hc' := lower_core (cR := cR) (A := c) (y := y) (v := y - δ) hs (by linarith) (by linarith)
      (by linarith) hcR.le (by linarith) (by linarith)
    rw [cdf_eq_one_sub L]; linarith

lemma caseC {s c ε cL εL w : ℝ} (L : Measure ℝ) [IsProbabilityMeasure L] (hs : 0 < s)
    (hc : 0 < c) (hcs : 5 * c ≤ s) (hcε : c * ε ≤ 1/4) (hεL0 : 0 < εL) (hεL : ε ≤ εL / 2)
    (hcL : 0 < cL) (h16 : 16 * cL ≤ c)
    (hLft : ∀ y : ℝ, s ≤ y → y ≤ εL * s^2 →
      L.real (Iio (-y)) ≤ (1 - Ncdf (y / s)) * Real.exp (cL * (y^3 / (s^2)^2)) ∧
      (1 - Ncdf (y / s)) * Real.exp (-(cL * (y^3 / (s^2)^2))) ≤ L.real (Iio (-y)))
    (hw2 : 2 * s < w) (hwε : w ≤ ε * s^2) :
    Ncdf (-w / s) ≤ cdf L (-w + c * (1 + (-w)^2 / s^2)) ∧
      cdf L (-w - c * (1 + (-w)^2 / s^2)) ≤ Ncdf (-w / s) := by
  obtain ⟨hδ1, hδ2⟩ := delta_le hs hc hcs hcε hw2 hwε
  rw [neg_sq, neg_div, phi_neg]
  set δ := c * (1 + w^2 / s^2)
  have hX : 0 ≤ c * (w^2 / s^2) := by positivity
  have hδ0 : 0 < δ := by positivity
  have hεs : ε * s^2 ≤ εL / 2 * s^2 := mul_le_mul_of_nonneg_right hεL (sq_nonneg s)
  have hεLs : 0 ≤ εL * s^2 := by positivity
  constructor
  · have hv := (hLft (w - δ) (by linarith) (by linarith)).2
    have hc' := lower_core (cR := cL) (A := c) (y := w) (v := w - δ) hs (by linarith) (by linarith)
      (by linarith) hcL.le (by linarith) (by linarith)
    have h3 := cdf_ge_Iio L (-w + δ)
    rw [show -w + δ = -(w - δ) by ring] at h3 ⊢
    linarith
  · have hu := (hLft (w + δ / 2) (by linarith) (by linarith)).1
    have hc' := upper_core (cR := cL) (A := c / 2) (y := w) (u := w + δ / 2) hs (by linarith) (by linarith)
      (by linarith) hcL.le (by linarith) (by linarith)
    have h3 := cdf_le_Iio L (x := -w - δ) (x' := -(w + δ / 2)) (by linarith)
    linarith

end TusAux

open TusAux in
theorem solution :
    ∀ (cR εR cL εL K : ℝ),
      (0 : ℝ) < cR →
        (0 : ℝ) < εR →
          (0 : ℝ) < cL →
            (0 : ℝ) < εL →
              (0 : ℝ) < K →
                ∃ (c : ℝ) (ε : ℝ) (m₀ : ℕ),
                  (0 : ℝ) < c ∧
                    (0 : ℝ) < ε ∧
                      (1 : ℕ) ≤ m₀ ∧
                        ∀ (m : ℕ),
                          m₀ ≤ m →
                            ∀ (L : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure L],
                              (∀ (y : ℝ),
                                  √↑m ≤ y →
                                    y ≤ εR * ↑m →
                                      MeasureTheory.Measure.real L (Set.Ioi y) ≤
                                          ((1 : ℝ) -
                                              (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                (y / √↑m)) *
                                            Real.exp (cR * (y ^ (3 : ℕ) / ↑m ^ (2 : ℕ))) ∧
                                        ((1 : ℝ) -
                                              (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                (y / √↑m)) *
                                            Real.exp (-(cR * (y ^ (3 : ℕ) / ↑m ^ (2 : ℕ)))) ≤
                                          MeasureTheory.Measure.real L (Set.Ioi y)) →
                                (∀ (y : ℝ),
                                    √↑m ≤ y →
                                      y ≤ εL * ↑m →
                                        MeasureTheory.Measure.real L (Set.Iio (-y)) ≤
                                            ((1 : ℝ) -
                                                (ProbabilityTheory.cdf
                                                      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                  (y / √↑m)) *
                                              Real.exp (cL * (y ^ (3 : ℕ) / ↑m ^ (2 : ℕ))) ∧
                                          ((1 : ℝ) -
                                                (ProbabilityTheory.cdf
                                                      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                  (y / √↑m)) *
                                              Real.exp (-(cL * (y ^ (3 : ℕ) / ↑m ^ (2 : ℕ)))) ≤
                                            MeasureTheory.Measure.real L (Set.Iio (-y))) →
                                  (∀ (z : ℝ),
                                      |z| ≤ (3 : ℝ) →
                                        (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) z -
                                              K / √↑m ≤
                                            (ProbabilityTheory.cdf L) (√↑m * z) ∧
                                          (ProbabilityTheory.cdf L) (√↑m * z) ≤
                                            (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                                z +
                                              K / √↑m) →
                                    ∀ (y : ℝ),
                                      |y| ≤ ε * ↑m →
                                        (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                              (y / √↑m) ≤
                                            (ProbabilityTheory.cdf L) (y + c * ((1 : ℝ) + y ^ (2 : ℕ) / ↑m)) ∧
                                          (ProbabilityTheory.cdf L) (y - c * ((1 : ℝ) + y ^ (2 : ℕ) / ↑m)) ≤
                                            (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)))
                                              (y / √↑m) := by
  intro cR εR cL εL K hcR hεR hcL hεL hK
  set φ3 : ℝ := (√(2 * Real.pi))⁻¹ * Real.exp (-9/2) with hφ3
  have hφ : 0 < φ3 := by positivity
  set c : ℝ := K / φ3 + 16 * cR + 16 * cL + 1 with hcdef
  have hc : 0 < c := by positivity
  have hKφ : 0 ≤ K / φ3 := by positivity
  set ε : ℝ := min (min (εR / 2) (εL / 2)) (1 / (4 * c)) with hεdef
  have hε : 0 < ε := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  refine ⟨c, ε, ⌈25 * c^2⌉₊ + 1, hc, hε, by omega, ?_⟩
  intro m hm L _ hR hLft hBE y hy
  have hmR : (⌈25 * c^2⌉₊ : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hm25 : 25 * c^2 ≤ (m : ℝ) := by linarith [Nat.le_ceil (25 * c^2)]
  have hmpos : (0 : ℝ) < m := by nlinarith
  obtain ⟨s, hsdef⟩ : ∃ s, s = √(m : ℝ) := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 hmpos
  have hsm : (m : ℝ) = s^2 := by rw [hsdef, Real.sq_sqrt hmpos.le]
  have hcs : 5 * c ≤ s := by
    rw [hsdef]; exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith))
  rw [← hsdef] at hR hLft hBE ⊢
  rw [hsm] at hR hLft hy ⊢
  have hKc : K ≤ φ3 * c := by
    have : K = φ3 * (K / φ3) := by field_simp
    nlinarith
  have hcε : c * ε ≤ 1 / 4 := by
    have h1 : ε ≤ 1 / (4 * c) := min_le_right _ _
    have h2 : c * (1 / (4 * c)) = 1 / 4 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]
  have hεR' : ε ≤ εR / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hεL' : ε ≤ εL / 2 := (min_le_left _ _).trans (min_le_right _ _)
  by_cases hA : |y| ≤ 2 * s
  · exact caseA (cdf L) hs hc hcs hKc hBE hA
  · push Not at hA
    rcases lt_or_ge 0 y with hy0 | hy0
    · rw [abs_of_pos hy0] at hA
      rw [abs_of_pos hy0] at hy
      exact caseB L hs hc hcs hcε hεR hεR' hcR (by linarith) hR hA hy
    · rw [abs_of_nonpos hy0] at hA hy
      have := caseC (w := -y) L hs hc hcs hcε hεL hεL' hcL (by linarith) hLft hA hy
      simpa only [neg_neg] using this
