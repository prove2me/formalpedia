-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_source_compensated_band_tail_from_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:57:08.450452+00:00
-- url     : https://prove2.me/submissions/7ede889f-83f1-44b9-aa4d-b35834c538cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    [mAll : MeasurableSpace ((ℝ≥0 × Ω) × ℝ)]
    (μ : Measure ((ℝ≥0 × Ω) × ℝ))
    (hAll : mAll = (𝓕.predictable).prod
      (inferInstance : MeasurableSpace ℝ))
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ) (hGm : Measurable G)
    (hG : MemLp G (2 : ℝ≥0∞) μ)
    (hEnergy : ∫⁻ p, ‖G p‖ₑ ^ (2 : ℝ) ∂μ < ∞)
    (B : ℕ → Set ((ℝ≥0 × Ω) × ℝ))
    (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, μ (B n) < ∞)
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
    (I : Lp ℝ (2 : ℝ≥0∞) μ →ₗ[ℝ] Lp ℝ (2 : ℝ≥0∞) P)
    (hIso : ∀ v, ‖I v‖ = ‖v‖)
    (hZero : ∀ v, ∫ ω, I v ω ∂P = 0)
    (clock : Measure ℝ≥0)
    (hSource : ∀ n,
      (I ((hG.indicator (hB n)).toLp ((B n).indicator G)) : Ω → ℝ)
        =ᵐ[P] fun ω =>
      (∫ p, (B n).indicator G ((p.1, ω), p.2) ∂(NX ω)) -
        ∫ t, ∫ z, (B n).indicator G ((t, ω), z) ∂X.ν ∂clock) :
    ∃ Llimit : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto (fun n => I ((hG.indicator (hB n)).toLp
        ((B n).indicator G))) atTop (𝓝 Llimit) ∧
      (∫ ω, Llimit ω ∂P) = 0 ∧
      (∀ m n, m ≤ n →
        dist (I ((hG.indicator (hB m)).toLp ((B m).indicator G)))
          (I ((hG.indicator (hB n)).toLp ((B n).indicator G))) ≤
          (eLpNorm ((B m)ᶜ.indicator G) (2 : ℝ≥0∞) μ).toReal) ∧
      (∀ n,
        (I ((hG.indicator (hB n)).toLp ((B n).indicator G)) : Ω → ℝ)
          =ᵐ[P] fun ω =>
        (∫ p, (B n).indicator G ((p.1, ω), p.2) ∂(NX ω)) -
          ∫ t, ∫ z, (B n).indicator G ((t, ω), z) ∂X.ν ∂clock) := by
  let u : ℕ → Lp ℝ (2 : ℝ≥0∞) μ := fun n => (hG.indicator (hB n)).toLp ((B n).indicator G)
  let M : ℕ → Lp ℝ (2 : ℝ≥0∞) P := fun n => I (u n)
  have hb : ∀ m n, m ≤ n → dist (M m) (M n) ≤
      (eLpNorm ((B m)ᶜ.indicator G) (2 : ℝ≥0∞) μ).toReal := by
    intro m n hmn
    have ht : ‖u m - u n‖ ≤
        ‖(hG.indicator ((hB m).compl)).toLp ((B m)ᶜ.indicator G)‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(hG.indicator (hB m)).coeFn_toLp,
        (hG.indicator (hB n)).coeFn_toLp,
        (hG.indicator ((hB m).compl)).coeFn_toLp,
        Lp.coeFn_sub (u m) (u n)] with p hm hn hc hs
      simp only [hs, Pi.sub_apply]
      dsimp only [u]
      simp only [hm, hn, hc]
      by_cases hp : p ∈ B m
      · have hq : p ∈ B n := hBmono hmn hp
        simp_all [Set.indicator, norm_neg]
      · by_cases hq : p ∈ B n <;> simp_all [Set.indicator, norm_neg]
    calc
      dist (M m) (M n) = ‖I (u m - u n)‖ := by simp [M, dist_eq_norm, map_sub]
      _ = ‖u m - u n‖ := hIso _
      _ ≤ ‖(hG.indicator ((hB m).compl)).toLp ((B m)ᶜ.indicator G)‖ := ht
      _ = (eLpNorm ((B m)ᶜ.indicator G) (2 : ℝ≥0∞) μ).toReal :=
        Lp.norm_toLp ((B m)ᶜ.indicator G) (hG.indicator ((hB m).compl))
  obtain ⟨Llimit, hconv, hmean⟩ :=
    avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero
      P μ G hGm hEnergy B hB hBfinite hBmono hBcover M hb (fun n => hZero (u n))
  exact ⟨Llimit, hconv, hmean, hb, hSource⟩
