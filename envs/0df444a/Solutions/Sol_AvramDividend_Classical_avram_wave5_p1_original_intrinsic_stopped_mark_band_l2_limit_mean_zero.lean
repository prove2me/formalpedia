-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_p1_original_intrinsic_stopped_mark_band_l2_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:39:51.609243+00:00
-- url     : https://prove2.me/submissions/7eb9ee21-25d6-4cd5-bcbf-50a748c098bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_actual_source_stopped_signed_jump_compensation_of_rectangles
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
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (B : ℕ → Set ℝ) (hBm : ∀ n, MeasurableSet (B n))
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
    (hLocal : ∀ n, M ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B n) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      M (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      M ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (ν : Measure ℝ) (hBfinite : ∀ n, ν (B n) < ∞) (f : ℝ → ℝ) (hf : Measurable f)
    (henergy : ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂ν < ∞)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ) (Gband : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGband : ∀ n, Gband n = ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B n).indicator G)
    (hGm : ∀ n, Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] (Gband n))
    (hGi : ∀ n, Integrable (Gband n) M)
    (H : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : ∀ n, H n = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then Gband n p else 0)
    (hActualI : ∀ n, Integrable
      (fun ω => ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)) P)
    (hSourceFubini : ∀ n,
      (∫ ω, ∫ p, H n ((p.1, ω), p.2) ∂(NX ω) ∂P) =
        ∫ p, H n p ∂M)
    (V : ℕ → Ω → ℝ)
    (hV : ∀ n, V n = fun ω =>
      (∫ p, H n ((p.1, ω), p.2) ∂(NX ω)) -
        ∫ p, H n p ∂N)
    (L : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hRep : ∀ n, (L n : Ω → ℝ) =ᵐ[P] V n)
    (hbound : ∀ m n, m ≤ n →
      dist (L m) (L n) ≤
        (eLpNorm ((B m)ᶜ.indicator f) (2 : ℝ≥0∞) ν).toReal) :
    ∃ Llimit : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto L Filter.atTop (nhds Llimit) ∧
        (∫ ω, Llimit ω ∂P) = 0 := by
  have hsource (n : ℕ) :
      (∫ ω, ∫ p, H n ((p.1, ω), p.2) ∂(NX ω) ∂P) -
        (∫ p, H n p ∂N) = 0 := by
    obtain ⟨_, _, _, hzero⟩ :=
      AvramDividend.Classical.avram_wave5_p1_actual_source_stopped_signed_jump_compensation_of_rectangles
        X NX hNX M N B hBm hBmono hBcover hLocal hBot hFuture
        τ hτ (Gband n) (hGm n) (hGi n) (H n) (hH n)
        (hActualI n) (hSourceFubini n)
    exact hzero
  have hcenter (n : ℕ) : (∫ ω, (L n) ω ∂P) = 0 := by
    calc
      (∫ ω, (L n) ω ∂P) = ∫ ω, V n ω ∂P :=
        integral_congr_ae (hRep n)
      _ = 0 := by
        rw [hV n, integral_sub (hActualI n) (integrable_const _)]
        simpa [integral_const] using hsource n
  exact
    AvramDividend.Classical.avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero
      P ν f hf henergy B hBm hBfinite hBmono hBcover L hbound hcenter
