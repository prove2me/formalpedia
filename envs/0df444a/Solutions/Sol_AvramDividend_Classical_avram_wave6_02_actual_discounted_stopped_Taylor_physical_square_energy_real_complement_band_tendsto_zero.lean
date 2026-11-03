-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_physical_square_energy_real_complement_band_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:23:16.314175+00:00
-- url     : https://prove2.me/submissions/37238092-5638-4f0e-968a-22a6f24cb8a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_rightcont_product_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_stopped_Taylor_rightcont_physical_product_L1_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_square_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (B : ℕ → Set (((ℝ≥0 × Ω) × ℝ)))
        (hB : ∀ n, MeasurableSet (B n))
        (hBmono : Monotone B)
        (hBcover : (⋃ n, B n) = Set.univ),
      Tendsto (fun n =>
        ∫ p, ((B n)ᶜ).indicator (fun p => GW p ^ 2) p
          ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
        atTop (𝓝 (0 : ℝ))) := by
  classical
  intro a Y H HS GW
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  intro B hB hBmono hBcover
  let mprod : Measure ((ℝ≥0 × Ω) × ℝ) :=
    μ.prod (X.ν.restrict (Iio (0 : ℝ)))
  let E : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => GW p ^ 2
  have hInt : Integrable E mprod :=
    avram_wave6_02_actual_discounted_ruin_stopped_Taylor_predictable_square_integrable
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv q hq T μ hμ
  change Tendsto (fun n => ∫ p, ((B n)ᶜ).indicator E p ∂mprod)
    atTop (𝓝 (0 : ℝ))
  have hIntAbs : Integrable (fun p => |E p|) mprod := by
    simpa only [Real.norm_eq_abs] using hInt.norm
  have hMem (p : ((ℝ≥0 × Ω) × ℝ)) : ∃ n, p ∈ B n := by
    have hp : p ∈ ⋃ n, B n := by
      rw [hBcover]
      exact Set.mem_univ p
    simpa only [Set.mem_iUnion] using hp
  have hEv (p : ((ℝ≥0 × Ω) × ℝ)) :
      ∀ᶠ n in atTop, ((B n)ᶜ).indicator E p = 0 := by
    obtain ⟨n0, hp0⟩ := hMem p
    filter_upwards [eventually_ge_atTop n0] with n hn
    have hp : p ∈ B n := hBmono hn hp0
    exact Set.indicator_of_notMem (by simpa using hp) E
  have hPoint :
      ∀ᵐ p ∂mprod,
        Tendsto (fun n => ((B n)ᶜ).indicator E p) atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Eventually.of_forall
    intro p
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
      ((hEv p).mono (fun n hn => hn.symm))
  have hBound (n : ℕ) :
      ∀ᵐ p ∂mprod, ‖((B n)ᶜ).indicator E p‖ ≤ |E p| := by
    apply Filter.Eventually.of_forall
    intro p
    by_cases hp : p ∈ (B n)ᶜ
    · simp only [Set.indicator_of_mem hp, Real.norm_eq_abs, le_refl]
    · simp [Set.indicator_of_notMem hp]
  have hStrong (n : ℕ) :
      AEStronglyMeasurable (((B n)ᶜ).indicator E) mprod :=
    (hInt.indicator (hB n).compl).1
  have hDCT :=
    tendsto_integral_of_dominated_convergence
      (f := fun _ => (0 : ℝ))
      (bound := fun p => |E p|)
      hStrong hIntAbs hBound hPoint
  simpa only [integral_zero] using hDCT
