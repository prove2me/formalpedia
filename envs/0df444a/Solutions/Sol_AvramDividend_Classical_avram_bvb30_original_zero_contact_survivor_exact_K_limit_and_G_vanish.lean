-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb30_original_zero_contact_survivor_exact_K_limit_and_G_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:16:23.765557+00:00
-- url     : https://prove2.me/submissions/e1095505-54de-4478-892a-ca3dbcc0451f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb26_original_survival_zero_contact_full_K_exact_discounted_time_integral
import Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_zero_reserve_survival_strict_generator_grid_tendsto_zero_from_proved_children
import Theorems.Thm_AvramDividend_Classical_avram_bvb26_original_uniform_prefix_discounted_setIntegral_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0) (hgrid : ∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)))
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) (B : ℕ → Ω → ℝ)
    (hB : ∀ n ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      B n ω =
        (∑ i ∈ Finset.range (n + 1), if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) * (X.generator w (Z i) - q * w (Z i)) * ((u n (i + 1) : ℝ) - (u n i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
           ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
           else 0) * (R (u n i) - R (u n (i + 1)))))
    (hAllB : ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0)
    (hPre : ∀ᵐ ω ∂P, ∀ n i, Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n (i + 1)) = riskProcess X x D (u n (i + 1)) ω)
    (hFinite : C ≠ ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧ (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧ 0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) * (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω => ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map (fun t : ℝ≥0 => (t, X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let G : ℕ → Ω → ℝ := fun n ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      (∑ i ∈ Finset.range (n + 1),
          if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) * (X.generator w (Z i) - q * w (Z i)) * ((u n (i + 1) : ℝ) - (u n i : ℝ))
          else 0)
    let K : ℕ → Ω → ℝ := fun n ω => (∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal))
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0, t ≤ S → X.X t ω = (t : ℝ) * X.drift) → (NX ω) (Ioc (0 : ℝ≥0) S ×ˢ Iio (0 : ℝ)) = 0 →
      ((S : ℝ≥0∞) < ruinTime X x D ω) →
      (∀ t : ℝ≥0, t ≤ S → riskProcess X x D t ω = 0) →
      (Tendsto (fun n => K n ω) atTop (𝓝 (-(w 0 * (X.ν (Iio (0 : ℝ))).toReal) * (∫ t in Ioc (0 : ℝ) T, Real.exp (-(q * t)) ∂(volume : Measure ℝ))))) ∧
        Tendsto (fun n => G n ω) atTop (𝓝 (0 : ℝ))  := by
  intro δ S F U H NX G K
  filter_upwards [hPre] with ω hp
  intro hs hn hr hz
  have hBound (n i : ℕ) (hi : i ≤ n + 1) : u n i ≤ S := by
    apply NNReal.coe_le_coe.mp
    rw [huniform n i]
    have hd : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hiReal : (i : ℝ) ≤ (n : ℝ) + 2 := by
      exact_mod_cast (show i ≤ n + 2 by omega)
    apply (div_le_iff₀ hd).mpr
    have hMul := mul_le_mul_of_nonneg_left hiReal hT.le
    change T * (i : ℝ) ≤ (S : ℝ) * ((n : ℝ) + 2)
    simpa only [show (S : ℝ) = T from rfl] using hMul
  have hMesh : Tendsto (fun n : ℕ => (u n 1 : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    have hShift :=
      (Filter.tendsto_add_atTop_iff_nat
        (f := fun n : ℕ => T / (n : ℝ))
        (l := 𝓝 (0 : ℝ)) 2).2
        (tendsto_const_div_atTop_nhds_zero_nat T)
    have hDelta : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2))
        atTop (𝓝 (0 : ℝ)) := by
      simpa [Nat.cast_add] using hShift
    simpa [huniform] using hDelta
  have hGlimit : Tendsto (fun n : ℕ => G n ω)
      atTop (𝓝 (0 : ℝ)) := by
    exact avram_bvb24_original_zero_reserve_survival_strict_generator_grid_tendsto_zero_from_proved_children
      X x D w C q u ω S (fun n => (hgrid n).1) hBound hMesh hp hz
  have hKformula (n : ℕ) :
      K n ω = -(w 0 * (X.ν (Iio (0 : ℝ))).toReal) *
        (∫ t in Ioc (0 : ℝ) (T - T / ((n : ℝ) + 2)),
          Real.exp (-(q * t)) ∂(volume : Measure ℝ)) := by
    exact avram_bvb26_original_survival_zero_contact_full_K_exact_discounted_time_integral
      X x C D hD w hw_neg q T hT ω S rfl hs hz hr n
  have hKlimit : Tendsto (fun n : ℕ => K n ω)
      atTop (𝓝 (-(w 0 * (X.ν (Iio (0 : ℝ))).toReal) *
        (∫ t in Ioc (0 : ℝ) T,
          Real.exp (-(q * t)) ∂(volume : Measure ℝ)))) := by
    have hf : (fun n : ℕ => K n ω) =
        (fun n : ℕ => -(w 0 * (X.ν (Iio (0 : ℝ))).toReal) *
          (∫ t in Ioc (0 : ℝ) (T - T / ((n : ℝ) + 2)),
            Real.exp (-(q * t)) ∂(volume : Measure ℝ))) := by
      funext n
      exact hKformula n
    rw [hf]
    exact (avram_bvb26_original_uniform_prefix_discounted_setIntegral_tendsto
      q T hT).const_mul (-(w 0 * (X.ν (Iio (0 : ℝ))).toReal))
  exact ⟨hKlimit, hGlimit⟩
