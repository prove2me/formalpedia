-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward54_original_stopped_linear_mark_clock_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:07:02.738532+00:00
-- url     : https://prove2.me/submissions/886e9ca9-e61b-4c2a-8347-c6be41dad410

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
import Theorems.Thm_AvramDividend_Classical_avram_bvb73_actual_source_uniform_positive_time_pushforward_finite_mass
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_compact_derivative_bounded
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward57_finite_smallmark_clock_double_integral_uniform_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hSigmaZero : X.σ = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρle : ∀ ω, ρ ω ≤ τ ω) (G : Ω → ℝ) (hGdef : ∀ ω, G ω = (if ρ ω = 0 then w x else Real.exp (-(q * (ρ ω : ℝ))) * w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)) (hGI : Integrable G P) (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) (Cband u v δ η : ℝ)
    (hu : 0 < u) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (huv : u + δ < v) (hη : 0 < η) (hη1 : η < 1)
    (hv : v < Cband) (hvC : v < C.toReal)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband)) :
      (let T : ℝ≥0 := (n : ℝ≥0)
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
        (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then
          (1 : ℝ) else 0) * H p
      let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {s : ℝ≥0 | 0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
          (fun s : ℝ≥0 => (s, X.X s ω -
            Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
      let μT : Measure ℝ≥0 :=
        ((volume : Measure ℝ).restrict (Icc 0 ((n : ℝ≥0) : ℝ))).map Real.toNNReal
      let J : (Ω → ℝ≥0) → Ω → ℝ := fun ρ ω =>
        (∫ p, (if p.1 ≤ ρ ω then GW ((p.1, ω), p.2) else 0) ∂(NX ω)) -
        (∫ t, ∫ z,
          (if t ≤ ρ ω then GW ((t, ω), z) else 0)
          ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
      let R : ℝ≥0 × Ω → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) *
          ((if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
            (if Y p ∈ Icc (u + δ) v then
              X.generator w (Y p) - q * w (Y p) else 0))
      let B : (Ω → ℝ≥0) → Ω → ℝ := fun σ ω =>
        ∫ t : ℝ≥0, if t ≤ σ ω then R (t, ω) else 0 ∂μT
      let Lsource : Ω → ℝ := fun ω =>
        (∫ p, (if p.1 ≤ ρ ω ∧ p.2 ∈ Ioo (-1 : ℝ) (-η) then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if Y (p.1, ω) ∈ Icc (u + δ) v then
              deriv w (Y (p.1, ω)) * p.2 else 0) else 0) ∂(NX ω))
      let Lclock : Ω → ℝ := fun ω =>
        (∫ t, ∫ z,
          (if t ≤ ρ ω ∧ z ∈ Ioo (-1 : ℝ) (-η) then
            Real.exp (-(q * (t : ℝ))) *
              (if Y (t, ω) ∈ Icc (u + δ) v then
                deriv w (Y (t, ω)) * z else 0) else 0)
          ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μT)
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ᵐ ω ∂P, |Lclock ω| ≤ K)) := by
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim (fun s => x + X.X s p.2 - rightLimit D s p.2) p.1
  let μT : Measure ℝ≥0 := ((volume : Measure ℝ).restrict (Icc 0 ((n : ℝ≥0) : ℝ))).map Real.toNNReal
  let νB : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  let Z : Set ℝ := Ioo (-1 : ℝ) (-η)
  have hz : ∀ z ∈ Z, |z| ≤ 1 := by
    intro z hz; rw [abs_of_neg (lt_trans hz.2 (neg_neg_of_pos hη))]; linarith [hz.1]
  have hν : νB Z < ⊤ := by
    have ht := avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold X.ν X.ν_integrable η hη (le_of_lt hη1)
    have hb : X.ν Z < ⊤ := (measure_mono (fun z hz => le_of_lt hz.2)).trans_lt ht
    simpa [νB, Z, Measure.restrict_apply, measurableSet_Ioo,
      inter_eq_self_of_subset_left (show Z ⊆ Iio (0 : ℝ) from
        fun z hz => lt_trans hz.2 (neg_neg_of_pos hη))] using hb
  have hμ : μT Set.univ < ⊤ :=
    avram_bvb73_actual_source_uniform_positive_time_pushforward_finite_mass n (by exact_mod_cast hn)
  obtain ⟨M, hMd⟩ := avram_p4_c_generator_compact_derivative_bounded
    w Cband (u + δ) v hwCb (by linarith) hv
  have hM : 0 ≤ M := (abs_nonneg _).trans (hMd _ (left_mem_Icc.mpr (le_of_lt huv)))
  let K : ℝ := M * (νB Z).toReal * (μT Set.univ).toReal
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [] with ω
  let g : ℝ≥0 → ℝ := fun t => if Y (t, ω) ∈ Icc (u + δ) v then deriv w (Y (t, ω)) else 0
  have hg : ∀ t, |g t| ≤ M := by
    intro t; dsimp [g]; split_ifs with ht
    · exact hMd _ ht
    · simpa using hM
  have hb := avram_pj_reward57_finite_smallmark_clock_double_integral_uniform_bound
    μT hμ νB Z measurableSet_Ioo hν hz q (le_of_lt hq)
    (ρ ω) g M hM hg
  simpa [K, g, Y, μT, νB, Z, ite_mul, mul_assoc, and_comm, and_left_comm] using hb
