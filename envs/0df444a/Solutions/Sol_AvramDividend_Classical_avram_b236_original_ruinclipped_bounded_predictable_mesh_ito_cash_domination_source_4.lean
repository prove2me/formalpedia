-- Prove2me | solution 4 for AvramDividend.Classical.avram_b236_original_ruinclipped_bounded_predictable_mesh_ito_cash_domination_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:04:47.419158+00:00
-- url     : https://prove2.me/submissions/a34116a5-7fd3-41ed-a9c9-b0cacec5b7d9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_ruinclipped_signed_ito_mesh_L1_error_source
import Theorems.Thm_AvramDividend_Classical_avram_b24_two_channel_L1_cauchy_positive_error_geometric_subsequence
import Theorems.Thm_AvramDividend_Classical_avram_b24_generic_geometric_L1_gain_domination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
       Tendsto (fun k : ℕ =>
         avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
         atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
       Tendsto (fun k : ℕ =>
         avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
         atTop (𝓝 (Jsmall u ω))) :
    ∃ (MG MJ BG BJ : Ω → ℝ) (G J E : ℕ → Ω → ℝ),
      (∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (MG ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ))) ∧
      Integrable BG P ∧ Integrable BJ P ∧
      (∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω) ∧
      (∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ BJ ω) ∧
      (∀ k, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0)
        (WG WJ : ℕ → Ω → ℝ) (LG LJ : ℝ),
        (∀ i ∈ S, a i ≤ b i) ∧
        (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WG i)) ∧
        (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i)) ∧
        0 ≤ LG ∧ 0 ≤ LJ ∧
        (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG) ∧
        (∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ) ∧
        (∀ ω, G k ω =
          ∑ i ∈ S, (if σ ω ≤ a i then 0 else WG i ω) *
            (R (b i) ω - R (a i) ω)) ∧
        (∀ ω, J k ω =
          ∑ i ∈ S, (if σ ω ≤ a i then 0 else WJ i ω) *
            (Jsmall (b i) ω - Jsmall (a i) ω))) ∧
      (∀ k, ∀ᵐ ω ∂P,
        F ω ≤ w x + G k ω + J k ω + E k ω)  := by
  obtain ⟨G₀, J₀, E₀, hGI, hJI, hEI, hRep, hCash, hGC, hJC, hEC⟩ :=
    avram_b24_original_ruinclipped_signed_ito_mesh_L1_error_source
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn σ hσstop hσbound hσclip F hFsource hFI hFiniteActivity
      R Jsmall hRsource hJsource
  obtain ⟨s, hs, hGr, hJr, hEr⟩ :=
    avram_b24_two_channel_L1_cauchy_positive_error_geometric_subsequence
      G₀ J₀ E₀ hGC hJC hEC
  let G : ℕ → Ω → ℝ := fun k ω => G₀ (s k) ω
  let J : ℕ → Ω → ℝ := fun k ω => J₀ (s k) ω
  let E : ℕ → Ω → ℝ := fun k ω => E₀ (s k) ω
  have hGstep : ∀ k, Integrable (fun ω => G (k+1) ω - G k ω) P := by
    intro k; exact (hGI (s (k+1))).sub (hGI (s k))
  have hJstep : ∀ k, Integrable (fun ω => J (k+1) ω - J k ω) P := by
    intro k; exact (hJI (s (k+1))).sub (hJI (s k))
  obtain ⟨MG, MJ, BG, BJ, hGconv, hJconv, hEconv,
      hBG, hBJ, hGdom, hJdom⟩ :=
    avram_b24_generic_geometric_L1_gain_domination
      G J E (hGI (s 0)) (hJI (s 0))
      hGstep hJstep (fun k => hEI (s k)) hGr hJr hEr
  refine ⟨MG, MJ, BG, BJ, G, J, E,
    hGconv, hJconv, hEconv, hBG, hBJ, hGdom, hJdom, ?_, ?_⟩
  · intro k
    simpa only [G, J] using hRep (s k)
  · intro k
    simpa only [G, J, E] using hCash (s k)
