-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger139_original_clipped_postpayment_discount_euler_absolute_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:27:52.1568+00:00
-- url     : https://prove2.me/submissions/f02ada43-4f1b-4db9-b1d0-9953f92bd01a

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger160_original_clipped_discount_euler_grid_aestronglyMeasurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger161_original_clipped_discount_euler_pathwise_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let A : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      (∑ i ∈ Finset.range (m + 1),
        (E (v (i + 1)) - E (v i)) * w (Y (v i))) +
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then q * (Δ : ℝ) * E s * w (Y s) else 0
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => |A m ω|) P ∧
      (∫ ω, |A m ω| ∂P) ≤ ε := by
  intro A ε hε
  haveI : IsProbabilityMeasure P := X.isProbability
  have hMeas :=
    avram_gledger160_original_clipped_discount_euler_grid_aestronglyMeasurable
      X hX q hq w C hC hTopCap hw_smooth x hx hxc
      D hD n hn τ hτeq ρ hρstop hρle j hprefix
  obtain ⟨K, hK, hRate⟩ :=
    avram_gledger161_original_clipped_discount_euler_pathwise_rate
      X hX q hq w C hC hTopCap hw_smooth x hx hxc
      D hD n hn τ hτeq ρ hρstop hρle j hprefix
  obtain ⟨k, hk⟩ := exists_nat_gt (K / ε)
  refine ⟨k, ?_⟩
  intro m hkm
  have hmge : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hbound : K / ((m : ℝ) + 1) ≤ ε := by
    apply (div_le_iff₀ hden).mpr
    have hk' : K < ε * (k : ℝ) := by
      have hkreal : K / ε < (k : ℝ) := hk
      have hprod : K < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hkreal
      nlinarith
    nlinarith
  have hnonneg : 0 ≤ K / ((m : ℝ) + 1) := div_nonneg hK hden.le
  have hA := hRate m
  have hnorm : ∀ᵐ ω ∂P,
      ‖|A m ω|‖ ≤ K / ((m : ℝ) + 1) := by
    filter_upwards [hA] with ω hω
    simpa only [Real.norm_eq_abs, abs_abs] using hω
  have hAM : AEStronglyMeasurable (fun ω => |A m ω|) P := by
    simpa only [Real.norm_eq_abs] using (hMeas m).norm
  have hInt : Integrable (fun ω => |A m ω|) P :=
    (integrable_const (K / ((m : ℝ) + 1))).mono' hAM hnorm
  have hIntegral : (∫ ω, |A m ω| ∂P) ≤ K / ((m : ℝ) + 1) := by
    calc
      (∫ ω, |A m ω| ∂P) ≤ (∫ ω : Ω, K / ((m : ℝ) + 1) ∂P) :=
        integral_mono_ae hInt (integrable_const _) hA
      _ = K / ((m : ℝ) + 1) := by simp
  exact ⟨hInt, hIntegral.trans hbound⟩
