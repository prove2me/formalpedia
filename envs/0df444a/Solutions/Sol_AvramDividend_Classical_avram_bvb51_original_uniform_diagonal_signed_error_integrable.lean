-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb51_original_uniform_diagonal_signed_error_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:15:18.060305+00:00
-- url     : https://prove2.me/submissions/63c818bc-d9d0-405f-9eda-4f373647088e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb49_original_real_toNNReal_uniform_physical_grid
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys39_original_fullmask_jump_and_intensity_L1_equal_mean
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_canonical_strict_prefix_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys26_original_finite_activity_exact_B_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 < T)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hIntensityPositive : 0 < X.ν (Iio (0 : ℝ)))
    (hCapFinite : C ≠ ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let J : ℕ → Ω → ℝ := fun n ω =>
      ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
    let V : ℕ → Ω → ℝ := fun n ω =>
      ∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    let M : ℕ → Ω → ℝ := fun k ω => J k ω - V k ω
    let u : ℕ → ℕ → ℝ≥0 := fun n i => Real.toNNReal (T * (i : ℝ) / ((n : ℝ) + 2))
    let B : ℕ → Ω → ℝ := fun n ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * (X.generator w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) +
      (let J : ℝ≥0 → ℝ := fun t =>
         ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
       let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (n + 1),
         (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
           Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i) else 0) * (R (u n i) - R (u n (i + 1))))
    ∀ k : ℕ, Integrable (fun ω => max (F k ω - (w x + (M k ω + B k ω))) (0 : ℝ)) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro δ S F U H NX J V M u B k
  have hu := avram_bvb49_original_real_toNNReal_uniform_physical_grid T hT
  rcases hu with ⟨hgrid, hmono, huniform⟩
  have hFI : ∀ j : ℕ, Integrable (F j) P := by
    simpa only [δ, S, F] using
      avram_p3_comp8_original_canonical_strict_prefix_integrable
        X hBV x C D hD w hw_cont hw_neg q hq T hT hw_nonneg
  have hJV : ∀ j : ℕ, Integrable (J j) P ∧ Integrable (V j) P ∧
      (∫ ω, J j ω ∂P) = (∫ ω, V j ω ∂P) := by
    simpa only [δ, U, H, NX, J, V] using
      avram_bvb_phys39_original_fullmask_jump_and_intensity_L1_equal_mean
        X hBV q (le_of_lt hq) w C hC hCapFinite hw_cont hw_neg x D hD T hT hFinite
  have hBI : ∀ j : ℕ, Integrable (B j) P := by
    simpa only [u, B] using
      avram_bv_phys26_original_finite_activity_exact_B_integrable
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump T hT
        u hgrid hmono huniform B (by intro n ω Z; rfl) hCapFinite hFinite
  have hMI : Integrable (M k) P := (hJV k).1.sub (hJV k).2.1
  have hSub : Integrable (fun ω => F k ω - (w x + (M k ω + B k ω))) P := by
    exact (hFI k).sub ((integrable_const (w x)).add (hMI.add (hBI k)))
  exact hSub.pos_part
