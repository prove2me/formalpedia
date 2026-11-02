-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_discounted_chronological_source_intrinsic_nonlinear_band_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T16:03:47.978829+00:00
-- url     : https://prove2.me/submissions/2c9bc11d-aa62-4249-a1fe-d8b4e5f04134

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_bounded_time_weight_signed_intrinsic_band
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_source_band_discounted_chronological_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- A discounted chronological source-jump/dividend inequality for the
original controlled reserve, expressed with the signed intrinsic nonlinear
source marked integral. This retains the right-dividend admissibility input. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ) (C u v δ : ℝ) (hw : ContDiffOn ℝ 2 w (Ioo 0 C)) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y : ℝ, y < 0 → w y = 0) (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1) (huv : u + δ < v) (hv : v < C) (hjump : ∀ η (r : ℝ≥0), (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D η) → rightLimit D r η - D r η ≤ w (riskProcess X x D r η) - w (riskProcess X x D r η - (rightLimit D r η - D r η))) (q : ℝ) (hq : 0 ≤ q) (s t : ℝ≥0) (ω : Ω) (B : Set ℝ) (hBm : MeasurableSet B) (hBneg : B ⊆ Iio (0 : ℝ)) (ε : ℝ) (hε : 0 < ε) (hBsep : ∀ z ∈ B, ε ≤ dist z 0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => (if Y p.1 ∈ Icc (u + δ) v then w (Y p.1 + p.2) - w (Y p.1) else 0) - (if -1 < p.2 then p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0) else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let J : ℝ≥0 → Ω → ℝ := fun r η => X.X r η - Function.leftLim (fun z : ℝ≥0 => X.X z η) r
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun η => ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ J r η ≠ 0}).map (fun r : ℝ≥0 => (r, J r η)))
    let Gq : ℝ≥0 × ℝ → ℝ := fun p => if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then Real.exp (-(q * (p.1 : ℝ))) * HS ((p.1,ω),p.2) else 0
    let W : ℝ≥0 → ℝ := fun r => if (r : ℝ≥0∞) < ruinTime X x D ω then x + X.X r ω - rightLimit D r ω else riskProcess X x D r ω
    let cash : ℝ≥0 → ℝ := fun r => if (r : ℝ≥0∞) < ruinTime X x D ω then rightLimit D r ω - D r ω else 0
    let Lq : ℝ≥0 → ℝ := fun r => if (r : ℝ≥0∞) ≤ ruinTime X x D ω then Real.exp (-(q * (r : ℝ))) * (if -1 < J r ω then J r ω * (if Y (r,ω) ∈ Icc (u + δ) v then deriv w (Y (r,ω)) else 0) else 0) else 0
    ∃ T : Finset ℝ≥0, (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧ Integrable Gq (NX ω) ∧ (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then (if Y (r,ω) ∈ Icc (u + δ) v then Real.exp (-(q * (r : ℝ))) * ((w (W r) - w (Function.leftLim (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r) else 0) else 0) ≤ (∑ r ∈ T, Lq r) + (∫ p : ℝ≥0 × ℝ, Gq p ∂NX ω) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p =>
    Function.leftLim (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0) else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let J : ℝ≥0 → Ω → ℝ := fun r η =>
    X.X r η - Function.leftLim (fun z : ℝ≥0 => X.X z η) r
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun η =>
    ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ J r η ≠ 0}).map
      (fun r : ℝ≥0 => (r, J r η)))
  let a : ℝ≥0 → ℝ := fun r => Real.exp (-(q * (r : ℝ)))
  let Gq : ℝ≥0 × ℝ → ℝ := fun p =>
    if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then a p.1 * HS ((p.1,ω),p.2) else 0
  let W : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X r ω - rightLimit D r ω else riskProcess X x D r ω
  let cash : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) < ruinTime X x D ω then
      rightLimit D r ω - D r ω else 0
  let L : ℝ≥0 → ℝ := fun r =>
    if -1 < J r ω then J r ω *
      (if Y (r,ω) ∈ Icc (u + δ) v then deriv w (Y (r,ω)) else 0) else 0
  let K : ℝ≥0 → ℝ := fun r =>
    if Y (r,ω) ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y (r,ω)) (J r ω) else 0
  let Lq : ℝ≥0 → ℝ := fun r =>
    if (r : ℝ≥0∞) ≤ ruinTime X x D ω then a r * L r else 0
  change ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable Gq (NX ω) ∧
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y (r,ω) ∈ Icc (u + δ) v then
          a r * ((w (W r) -
            w (Function.leftLim (fun z : ℝ≥0 => riskProcess X x D z ω) r)) + cash r)
          else 0) else 0) ≤
      (∑ r ∈ T, Lq r) + (∫ p : ℝ≥0 × ℝ, Gq p ∂NX ω)
  have ha : Measurable a := by
    fun_prop
  have hbound (r : ℝ≥0) : |a r| ≤ (1 : ℝ) := by
    dsimp only [a]
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (mul_nonneg hq (NNReal.coe_nonneg r))
  obtain ⟨T, hT, hInt, hSigned⟩ :=
    avram_wave5_03b_actual_ruin_stopped_bounded_time_weight_signed_intrinsic_band
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      s t ω B hBm hBneg ε hε hBsep a ha 1 hbound
  obtain ⟨T', hT', hChron⟩ :=
    avram_wave5_03b_actual_separated_source_band_discounted_chronological_bound
      X x D hD w hjump q u v δ s t ω B hBneg ε hε hBsep
  have hT'eq : T' = T := by
    ext r
    exact (hT' r).trans (hT r).symm
  rw [hT'eq] at hChron
  have hGen (r : ℝ≥0) (hr : r ∈ T) :
      H ((r,ω),J r ω) = K r := by
    have hrB : J r ω ∈ B := ((hT r).mp hr).2.2
    have hneg : J r ω < 0 := hBneg hrB
    simpa only [Y, H, J, K] using
      (avram_wave5_03b_actual_source_taylor_generator_kernel_eq
        X x D hD w u v δ (r,ω) (J r ω) hneg)
  have hHS (r : ℝ≥0) (hr : r ∈ T) :
      HS ((r,ω),J r ω) =
        if (r : ℝ≥0∞) ≤ ruinTime X x D ω then K r else 0 := by
    change (if (r : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0) *
      H ((r,ω),J r ω) = _
    rw [hGen r hr]
    split_ifs <;> simp
  have hsplit (r : ℝ≥0) (hr : r ∈ T) :
      (if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y (r,ω) ∈ Icc (u + δ) v then
          a r * ((if -1 < J r ω then
            J r ω * deriv w (Y (r,ω)) else 0) +
            SpectrallyNegativeLevy.generatorIntegrand w (Y (r,ω)) (J r ω))
          else 0) else 0) =
      Lq r + a r * HS ((r,ω),J r ω) := by
    rw [hHS r hr]
    by_cases hs : (r : ℝ≥0∞) ≤ ruinTime X x D ω
    · by_cases hl : Y (r,ω) ∈ Icc (u + δ) v
      · have hpair : u + δ ≤ Y (r,ω) ∧ Y (r,ω) ≤ v := by
          simpa only [Set.mem_Icc] using hl
        by_cases hj : -1 < J r ω
        · simp [hs, hl, hpair.1, hpair.2, hj, Lq, L, K, mul_add] <;> ring
        · simp [hs, hl, hpair.1, hpair.2, hj, Lq, L, K, mul_add] <;> ring
      · have hnotpair : ¬ (u + δ ≤ Y (r,ω) ∧ Y (r,ω) ≤ v) := by
          simpa only [Set.mem_Icc] using hl
        simp [hs, hl, hnotpair, Lq, L, K]
    · simp [hs, Lq]
  have hChron' :
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y (r,ω) ∈ Icc (u + δ) v then
          a r * ((w (W r) -
            w (Function.leftLim (fun z : ℝ≥0 => riskProcess X x D z ω) r)) + cash r)
          else 0) else 0) ≤
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y (r,ω) ∈ Icc (u + δ) v then
          a r * ((if -1 < J r ω then J r ω * deriv w (Y (r,ω)) else 0) +
            SpectrallyNegativeLevy.generatorIntegrand w (Y (r,ω)) (J r ω))
          else 0) else 0) := by
    simpa only [Y, J, W, cash, a] using hChron
  refine ⟨T, hT, hInt, ?_⟩
  apply hChron'.trans_eq
  calc
    (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y (r,ω) ∈ Icc (u + δ) v then
        a r * ((if -1 < J r ω then J r ω * deriv w (Y (r,ω)) else 0) +
          SpectrallyNegativeLevy.generatorIntegrand w (Y (r,ω)) (J r ω))
      else 0) else 0) =
      (∑ r ∈ T, (Lq r + a r * HS ((r,ω),J r ω))) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hsplit r hr
    _ = (∑ r ∈ T, Lq r) +
      (∑ r ∈ T, a r * HS ((r,ω),J r ω)) := Finset.sum_add_distrib
    _ = _ := by rw [hSigned]
