-- Prove2me | solution 3 for AvramDividend.Classical.avram_p3_comp8_original_uniform_two_error_source_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:56:26.236238+00:00
-- url     : https://prove2.me/submissions/45d0c85b-f625-490e-b487-7f671bac3960
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_cofinal_band_uniform_compensated_M
import Theorems.Thm_AvramDividend_Classical_avram_bv_tail12_original_given_cofinal_positive_error_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_canonical_strict_prefix_integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0) (hgrid : ∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) (B : ℕ → Ω → ℝ)
    (hB : ∀ n ω,
        let Z : ℕ → ℝ := fun i => Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
        B n ω =
          (∑ i ∈ Finset.range (n + 1),
            if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
              Real.exp (-(q * (u n i : ℝ))) * (X.generator w (Z i) - q * w (Z i)) *
                ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) +
          (let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0
           let R : ℝ≥0 → ℝ := fun t =>
             ((t : ℝ) * X.drift - X.X t ω) - J t
           ∑ i ∈ Finset.range (n + 1), (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
                 0 < Z i ∧ ENNReal.ofReal (Z i) < C then
               Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
             else 0) * (R (u n i) - R (u n (i + 1))))) (hBI : ∀ n, Integrable (B n) P) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)
    ∃ M ErrCell ErrContact : ℕ → Ω → ℝ, (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (ErrCell n ω) 0) P) ∧
      (∀ n, Integrable (fun ω => max (ErrContact n ω) 0) P) ∧ (∀ n, ∀ᵐ ω ∂P, F n ω ≤
        w x + (M n ω + B n ω) + max (ErrCell n ω) 0 + max (ErrContact n ω) 0) ∧
      Tendsto (fun n => ∫ ω, max (ErrCell n ω) 0 ∂P) atTop (nhds (0 : ℝ)) ∧
      Tendsto (fun n => ∫ ω, max (ErrContact n ω) 0 ∂P) atTop (nhds (0 : ℝ)) := by
  intro δ S F; letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨a, b, ha, ha2, hab, hinside, hcover, hMart⟩ :=
    avram_p3_comp8_original_cofinal_band_uniform_compensated_M
      X hBV q hq w C hC hw_cont hw_neg hw_smooth hw_gen
      x D hD T hT u (fun n => (hgrid n).1) huniform
  let M : ℕ → Ω → ℝ := fun n ω =>
    let K : ℝ≥0 → Ω → ℝ := fun S ω =>
      let τ : Ω → ℝ≥0 := fun ω' =>
        (min (ruinTime X x D ω') (S : ℝ≥0∞)).toNNReal
      let E : Set (ℝ≥0 × Ω) := {p |
        (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧ Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
      let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if p.1 ∈ E ∧ p.2 < 0 then Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
        else 0
      let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω' =>
        ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧
            X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v ≠ 0}).map (fun v : ℝ≥0 => (v,
            X.X v ω' - Function.leftLim (fun r : ℝ≥0 => X.X r ω') v)))
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (S : ℝ))).map Real.toNNReal))
    Finset.sum (Finset.range (n + 1)) (fun i => K (u n (i + 1)) ω - K (u n i) ω)
  have hMI (n : ℕ) : Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0 := hMart n
  let E : ℕ → Ω → ℝ := fun n ω => max (F n ω - (w x + (M n ω + B n ω))) 0
  have hFI := avram_p3_comp8_original_canonical_strict_prefix_integrable
      X hBV x C D hD w hw_cont hw_neg q hq T hT hw_nonneg
  have hEI (n : ℕ) : Integrable (E n) P := by
    have hc : Integrable (fun _ : Ω => w x) P := integrable_const (w x)
    have hb : Integrable (fun ω => w x + (M n ω + B n ω)) P := hc.add ((hMI n).1.add (hBI n))
    exact ((hFI n).sub hb).pos_part
  have hMean := avram_bv_tail12_original_given_cofinal_positive_error_L1
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT u hgrid hmono huniform
      B hB hBI a b ha ha2 hab hinside hcover
  refine ⟨M, E, (fun _ _ => (0 : ℝ)), hMI, ?_, ?_, ?_, ?_, ?_⟩
  · intro n; simpa only [E, max_assoc, max_self] using hEI n
  · intro n; simpa using (integrable_zero : Integrable (fun _ : Ω => (0 : ℝ)) P)
  · intro n
    filter_upwards [] with ω
    have hNonneg : 0 ≤ E n ω := le_max_right _ _
    change F n ω ≤ w x + (M n ω + B n ω) + max (E n ω) 0 + max (0 : ℝ) 0
    simp only [max_eq_left hNonneg, max_self, add_zero]
    dsimp [E]
    linarith [le_max_left (F n ω - (w x + (M n ω + B n ω))) (0 : ℝ)]
  · simpa only [E, max_assoc, max_self] using hMean
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
