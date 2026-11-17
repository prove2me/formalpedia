-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_positive_clock_cash_source_integrability_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:30:46.661202+00:00
-- url     : https://prove2.me/submissions/2fcee503-1ff5-4d6b-a3d1-36ac609a04ae

import Theorems.Thm_AvramDividend_Classical_avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_gfinite42_original_compact_diagonal_gaussian_grid_centered
import Theorems.Thm_AvramDividend_Classical_avram_gb26_original_finitecap_strip_event_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_gbB54cp_true_physical_gaussian_source_lower_clip_coefficients_sum_rewrite
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω) (δ : ℝ) (hδ : 0 < δ) (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω),
    ∀ (j : ℕ),
      let M : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        let a : ℝ := δ / 2
        let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        let Y : ℕ → Ω → ℝ := fun i η => x + X.X (s i) η - rightLimit D (s i) η
        let Z : ℕ → Ω → ℝ := fun i η => X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c
        let G : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then Real.exp (-(q * (s i : ℝ))) * (if Y i η ≤ b then deriv w (Y i η) else 1)
          else 0
        let H : ℕ → Ω → ℝ := fun i η =>
          if s i < ρ η then (1 / 2 : ℝ) * Real.exp (-(q * (s i : ℝ))) *
            (if Y i η ≤ b then iteratedDeriv 2 w (Y i η) else 0)
          else 0
        (Finset.range (m + 1)).sum (fun i => G i ω * Z i ω + H i ω *
            (Z i ω ^ 2 - (Δ : ℝ) * X.σ ^ 2))
      let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let F : Ω → ℝ := fun ω =>
          if ρ ω = 0 then w x else
            Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) +
            (∫⁻ z in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * z)))
              ∂(dividendMeasure D ω)).toReal
      let Occ : Ω → ℝ := fun ω =>
          ∫ t in Ioo (0 : ℝ) (n : ℝ),
            if t < (ρ ω : ℝ) ∧ b < riskProcess X x D (Real.toNNReal t) ω
            then (1 : ℝ) else 0 ∂volume
      let A : Set Ω := {ω | 0 < ρ ω}
      MeasurableSet A ∧ Integrable F P ∧
        (∀ m : ℕ, Integrable (M m) P) ∧ IntegrableOn Occ A P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k ρ hρstop hρle δ hδ hFloor j M b F Occ
  let A : Set Ω := {ω | 0 < ρ ω}
  have hZ : MeasurableSet[𝓕.rightCont 0] {ω : Ω | ρ ω = 0} := by
    have heq : {ω : Ω | (ρ ω : WithTop ℝ≥0) = 0} =
        {ω : Ω | ρ ω = 0} :=
      Set.ext (fun ω => by simp only [Set.mem_setOf_eq, WithTop.coe_eq_zero])
    have ht : MeasurableSet[𝓕.rightCont 0]
        {ω : Ω | (ρ ω : WithTop ℝ≥0) = 0} :=
      hρstop.measurableSet_eq (0 : ℝ≥0)
    rw [heq] at ht; exact ht
  have hAeq : {ω : Ω | ρ ω = 0}ᶜ = A := by
    ext ω; change (ρ ω ≠ 0) ↔ (0 < ρ ω); exact pos_iff_ne_zero.symm
  have hA0 : MeasurableSet[𝓕.rightCont 0] A := by
    rw [← hAeq]; exact hZ.compl
  have hA : MeasurableSet A := MeasureTheory.measurableSet_of_filtration hA0
  have hτbound (ω) : τ ω ≤ (n : ℝ≥0) := by
    rw [hτeq ω]; exact (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
  have hρbound (ω) : ρ ω ≤ (n : ℝ≥0) :=
    (hρle ω).trans ((hσle k ω).trans (hτbound ω))
  have hF : Integrable F P := by
    simpa only [F] using
      (avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
        X x C hFiniteCap hxc D hD w hw_cont hw_neg q hq ρ hρstop n hρbound)
  have hEq (m : ℕ) (ω : Ω) :=
    avram_gbB54cp_true_physical_gaussian_source_lower_clip_coefficients_sum_rewrite
      X x D hD.1.1 ρ δ hδ hFloor q w C j n m ω
  have hM (m : ℕ) : Integrable (M m) P := by
    let S : ℕ → ℕ := fun _ => m
    have hLower :=
      (avram_gfinite42_original_compact_diagonal_gaussian_grid_centered
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        n hn τ hτeq hτmeas hτstop σ hσstop hσle
        k ρ hρstop hρle δ hδ hFloor Set.univ MeasurableSet.univ S).1 j
    simp_rw [hEq] at hLower
    simpa only [M, S, integrableOn_univ] using hLower
  have hOcc : IntegrableOn Occ A P := by
    simpa only [Occ, b] using
      (avram_gb26_original_finitecap_strip_event_integrable
        X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor A hA0 j).1
  exact ⟨hA, hF, hM, hOcc⟩
