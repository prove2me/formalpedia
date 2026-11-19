-- Prove2me | solution 4 for AvramDividend.Classical.avram_b24_original_ruinclipped_positive_gap_ito_mesh_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:29:42.941296+00:00
-- url     : https://prove2.me/submissions/2075128f-b586-4dc4-b78e-72aa0d6a5d7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja20261118_original_finite_mixed_physical_mesh_L1_budget
import Theorems.Thm_AvramDividend_Classical_avram_b24_two_channel_L1_cauchy_positive_error_geometric_subsequence
import Theorems.Thm_AvramDividend_Classical_avram_b24_signed_ito_ledger_error_controls_positive_cash_gap_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
 SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ :
 X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont :
 ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧
 ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y
 ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
 (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
 (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
 (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w
 (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0
 < n) (σ : Ω → ℝ≥0) (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) (hσbound :
 ∀ ω, σ ω ≤ (n : ℝ≥0)) (hσclip : ∀ ω, σ ω ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (F : Ω →
 ℝ) (hFsource : ∀ ω, F ω = Real.exp (-(q * (σ ω : ℝ))) * w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X
 x D ω then x + X.X (σ ω) ω - rightLimit D (σ ω) ω else riskProcess X x D (σ ω) ω) + (∫⁻ s in
 paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))
 ∂(dividendMeasure D ω)).toReal) (hFI : Integrable F P) (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
 (R Jsmall : ℝ≥0 → Ω → ℝ) (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto (fun k : ℕ =>
 avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω) atTop (𝓝 (R u ω))) (hJsource : ∀ᵐ ω ∂P,
 ∀ u : ℝ≥0, Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
 atTop (𝓝 (Jsmall u ω))) : ∃ (G J : ℕ → Ω → ℝ), Integrable (G 0) P ∧ Integrable (J 0) P ∧ (∀ k,
 Integrable (fun ω => G (k + 1) ω - G k ω) P) ∧ (∀ k, Integrable (fun ω => J (k + 1) ω - J k ω) P)
 ∧ (∀ k, (∫ ω, ‖G (k + 1) ω - G k ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) ∧ (∀ k, (∫ ω, ‖J (k + 1) ω - J k ω‖
 ∂P) ≤ ((1 : ℝ) / 2) ^ k) ∧ (∀ k, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0) (WG WJ : ℕ → Ω → ℝ) (LG LJ : ℝ),
 (∀ i ∈ S, a i ≤ b i) ∧ (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i)) ∧ (∀ i ∈ S,
 Measurable[𝓕.rightCont (a i)] (WJ i)) ∧ 0 ≤ LG ∧ 0 ≤ LJ ∧ (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG) ∧ (∀ i ∈
 S, ∀ ω, ‖WJ i ω‖ ≤ LJ) ∧ (∀ ω, G k ω = ∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R
 (a i) ω)) ∧ (∀ ω, J k ω = ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) * (Jsmall (b i) ω - Jsmall (a
 i) ω))) ∧ (∀ k, Integrable (fun ω => max 0 (F ω - w x - G k ω - J k ω)) P) ∧ (∀ k, (∫ ω, ‖max 0 (F
 ω - w x - G k ω - J k ω)‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) := by
  obtain ⟨G, J, E, hGI, hJI, hEI, hGC, hJC, hEsmall, hMesh, hLedger⟩ :=
    avram_ja20261118_original_finite_mixed_physical_mesh_L1_budget
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg
      hjump n hn σ hσstop hσbound F hFsource hFI
      hFiniteActivity R Jsmall hRsource hJsource
  obtain ⟨s, hs, hGG, hJJ, hEE⟩ :=
    avram_b24_two_channel_L1_cauchy_positive_error_geometric_subsequence
      G J E hGC hJC hEsmall
  let G' : ℕ → Ω → ℝ := fun k => G (s k)
  let J' : ℕ → Ω → ℝ := fun k => J (s k)
  have hG0 : Integrable (G' 0) P := hGI (s 0)
  have hJ0 : Integrable (J' 0) P := hJI (s 0)
  have hGdiff : ∀ k, Integrable (fun ω => G' (k + 1) ω - G' k ω) P := by
    intro k
    exact (hGI (s (k + 1))).sub (hGI (s k))
  have hJdiff : ∀ k, Integrable (fun ω => J' (k + 1) ω - J' k ω) P := by
    intro k
    exact (hJI (s (k + 1))).sub (hJI (s k))
  have hGgeo : ∀ k, (∫ ω, ‖G' (k + 1) ω - G' k ω‖ ∂P) ≤
      ((1 : ℝ) / 2) ^ k := hGG
  have hJgeo : ∀ k, (∫ ω, ‖J' (k + 1) ω - J' k ω‖ ∂P) ≤
      ((1 : ℝ) / 2) ^ k := hJJ
  have hMeshes : ∀ k, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
      (WG WJ : ℕ → Ω → ℝ) (LG LJ : ℝ),
      (∀ i ∈ S, a i ≤ b i) ∧
      (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i)) ∧
      (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i)) ∧
      0 ≤ LG ∧ 0 ≤ LJ ∧
      (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG) ∧
      (∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ) ∧
      (∀ ω, G' k ω = ∑ i ∈ S,
        (if σ ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R (a i) ω)) ∧
      (∀ ω, J' k ω = ∑ i ∈ S,
        (if σ ω ≤ a i then 0 else WJ i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)) := by
    intro k
    exact hMesh (s k)
  have hGap : ∀ k, Integrable
      (fun ω => max 0 (F ω - w x - G' k ω - J' k ω)) P ∧
      (∫ ω, ‖max 0 (F ω - w x - G' k ω - J' k ω)‖ ∂P) ≤
        ((1 : ℝ) / 2) ^ k := by
    intro k
    obtain ⟨hI, hBound⟩ :=
      avram_b24_signed_ito_ledger_error_controls_positive_cash_gap_L1
        F (G (s k)) (J (s k)) (E (s k)) (w x)
        hFI (hGI (s k)) (hJI (s k)) (hEI (s k)) (hLedger (s k))
    exact ⟨hI, hBound.trans (hEE k)⟩
  exact ⟨G', J', hG0, hJ0, hGdiff, hJdiff, hGgeo, hJgeo,
    hMeshes, (fun k => (hGap k).1), (fun k => (hGap k).2)⟩
