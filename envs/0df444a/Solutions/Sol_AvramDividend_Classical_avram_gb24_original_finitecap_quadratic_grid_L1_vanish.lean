-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb24_original_finitecap_quadratic_grid_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:05:20.692302+00:00
-- url     : https://prove2.me/submissions/d425cb9c-2385-461c-a177-bcbe16b464ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gb28_original_finitecap_predictable_quadratic_grid_L2_rate
import Theorems.Thm_AvramDividend_Classical_avram_gb27_original_finitecap_quadratic_grid_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν
  = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth :
  ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y :
  ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
  (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
  w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω
  => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0) (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0)))
  (hσle : ∀ k ω, σ k ω ≤ τ ω) : ∀ k (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ σ k ω) (δ : ℝ) (hδ : 0 < δ) (hFloor : ∀ ω (t :
  ℝ≥0), 0 < t → t < ρ ω → δ ≤ riskProcess X x D t ω) (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
    ∀ (j : ℕ),
      let Q : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η =>
          x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η =>
          X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then deriv w (Y i η) else 1)
          else 0
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) *
            Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0)
          else 0
        (Finset.range (m + 1)).sum (fun i =>
          H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      Tendsto (fun m : ℕ =>
        ∫ ω in A, |Q m ω| ∂P) atTop (𝓝 (0 : ℝ)) := by
  classical
  intro k ρ hρstop hρle δ hδ hFloor A hA j
  let Q : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
    let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
    let H : ℕ → Ω → ℝ := fun i η =>
      if s i < ρ η then (1 / 2 : ℝ) *
        Real.exp (-(q * (s i : ℝ))) *
        (if Y i η ∈ Icc a b then iteratedDeriv 2 w (Y i η) else 0)
      else 0
    (Finset.range (m + 1)).sum (fun i => H i ω * (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
  change Tendsto (fun m : ℕ =>
    ∫ ω in A, |Q m ω| ∂P) atTop (𝓝 (0 : ℝ))
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨K, hK, hRate⟩ :=
    avram_gb28_original_finitecap_predictable_quadratic_grid_L2_rate
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA j
  have hUniv : MeasurableSet[𝓕.rightCont 0] (Set.univ : Set Ω) := MeasurableSet.univ
  have hQI (m : ℕ) : Integrable (Q m) P := by
    simpa [Q, IntegrableOn] using
      (avram_gb27_original_finitecap_quadratic_grid_integrable
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        n hn τ hτeq hτmeas hτstop σ hσstop hσle
        k ρ hρstop hρle δ hδ hFloor Set.univ hUniv j m)
  have hMoment (m : ℕ) : Integrable (fun ω => (Q m ω) ^ 2) P ∧
      (∫ ω, (Q m ω) ^ 2 ∂P) ≤ K / ((m + 1 : ℕ) : ℝ) := hRate m
  have hQ2 (m : ℕ) : MemLp (Q m) 2 P :=
    (memLp_two_iff_integrable_sq (hQI m).aestronglyMeasurable).2 (hMoment m).1
  have hRateZero : Tendsto
      (fun m : ℕ => K / ((m + 1 : ℕ) : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have heq : (fun m : ℕ => K / ((m + 1 : ℕ) : ℝ)) =
        (fun m : ℕ => K * ((1 : ℝ) / ((m : ℝ) + 1))) := by
      funext m
      simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul]
    rw [heq]
    simpa using ht.const_mul K
  have hEnergy : Tendsto (fun m : ℕ => ∫ ω, (Q m ω) ^ 2 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Tendsto.squeeze
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      hRateZero
    · intro m
      exact integral_nonneg (fun ω => sq_nonneg _)
    · intro m
      exact (hMoment m).2
  have hNormEq (m : ℕ) :
      lpNorm (Q m) 2 P =
        Real.sqrt (∫ ω, (Q m ω) ^ 2 ∂P) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (by norm_num) (by norm_num) (hQ2 m).aestronglyMeasurable]
    simp [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]
  have hLp2 : Tendsto (fun m : ℕ => lpNorm (Q m) 2 P) atTop (𝓝 (0 : ℝ)) := by
    have hc := (Real.continuous_sqrt.tendsto 0).comp hEnergy
    change Tendsto (fun m : ℕ => Real.sqrt
      (∫ ω, (Q m ω) ^ 2 ∂P)) atTop (𝓝 (Real.sqrt 0)) at hc
    have hsqrt : Tendsto (fun m : ℕ => Real.sqrt
        (∫ ω, (Q m ω) ^ 2 ∂P)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [Real.sqrt_zero] using hc
    simpa only [hNormEq] using hsqrt
  have hLpBound (m : ℕ) : lpNorm (Q m) 1 P ≤ lpNorm (Q m) 2 P := by
    have hENN := eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (hQ2 m).aestronglyMeasurable
    have hReal := ENNReal.toReal_mono (hQ2 m).eLpNorm_ne_top hENN
    simpa only [toReal_eLpNorm (hQ2 m).aestronglyMeasurable] using hReal
  have hLp1 : Tendsto (fun m : ℕ => lpNorm (Q m) 1 P)
      atTop (𝓝 (0 : ℝ)) := by
    apply Filter.Tendsto.squeeze
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      hLp2
    · intro m
      exact lpNorm_nonneg
    · exact hLpBound
  have hGlobal : Tendsto (fun m : ℕ => ∫ ω, |Q m ω| ∂P) atTop (𝓝 (0 : ℝ)) := by
    have heq (m : ℕ) :
        (∫ ω, |Q m ω| ∂P) = lpNorm (Q m) 1 P := by
      simpa only [Real.norm_eq_abs] using
        (lpNorm_one_eq_integral_norm
          (hQ2 m).aestronglyMeasurable).symm
    simpa only [heq] using hLp1
  apply Filter.Tendsto.squeeze
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    hGlobal
  · intro m
    exact integral_nonneg (fun ω => abs_nonneg _)
  · intro m
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun ω => abs_nonneg (Q m ω)))
      (hQI m).abs
