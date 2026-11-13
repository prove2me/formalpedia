-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_bv_actual_uniform_grid_discount_limit
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:17:03.211703+00:00
-- url     : https://prove2.me/submissions/36538a0a-89ba-43c7-b3b9-81ebadfcc1a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat24_original_shifted_pre_ruin_regulated_band
import Theorems.Thm_AvramDividend_Classical_avram_chat24_compact_left_limit_uniform_discount_Riemann
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hTop : C = ⊤) (δ : ℝ) (hδ : 0 < δ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let a : ℝ := min δ 1 / 2
    let b : ℝ := x + δ + T * X.drift + 1
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => (x + δ) + X.X s p.2 - rightLimit D s p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) ∧
          Y p.1 ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let μ : Measure ℝ≥0 :=
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∀ᵐ ω ∂P, ∀ B : ℝ≥0, 0 < B → B ≤ S →
      (B : ℝ≥0∞) < ruinTime X x D ω →
      Integrable (fun t : ℝ≥0 => if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y (t, ω) ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) * (-(q * w (Y (t, ω)))) else 0) μ ∧
      Tendsto (fun n : ℕ =>
        let N : ℕ := n + 1
        let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / (N : ℝ≥0)
        let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
        let U : ℕ → ℝ := fun i => riskProcess X x D (u i) ω + δ
        ∑ i ∈ Finset.range N, (e (i + 1) - e i) * w (U i))
        atTop (nhds ((∫ t : ℝ≥0, if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y (t, ω) ∈ Icc a b then
            Real.exp (-(q * (t : ℝ))) * (-(q * w (Y (t, ω)))) else 0 ∂μ))) := by
  classical
  intro S a b τ Y NX H μ
  have ha : 0 < a := by dsimp [a]; positivity
  have haδ : a ≤ δ := by dsimp [a]; linarith [min_le_left δ (1 : ℝ)]
  have hcont : ContinuousOn w (Icc a b) :=
    hw_cont.mono (fun y hy => ha.le.trans hy.1)
  filter_upwards [avram_chat24_original_shifted_pre_ruin_regulated_band
    X hX hBV x C D hD T hT δ] with ω hband
  intro B hB hBS hBruin
  obtain ⟨hreserve, hpre⟩ := hband B hBS hBruin
  have hreserve' (t : ℝ≥0) (ht : t ≤ B) :
      riskProcess X x D t ω + δ ∈ Icc a b := by
    have hh := hreserve t ht
    exact ⟨haδ.trans hh.1, hh.2.trans (by dsimp [b]; linarith)⟩
  have hpre' (t : ℝ≥0) (ht : 0 < t) (htB : t ≤ B) :
      Y (t, ω) ∈ Icc a b ∧
        Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω + δ)
          (𝓝[<] t) (nhds (Y (t, ω))) := by
    obtain ⟨hh, hl⟩ := hpre t ht htB
    exact ⟨⟨haδ.trans hh.1, hh.2.trans (by dsimp [b]; linarith)⟩, hl⟩
  simpa only using avram_chat24_compact_left_limit_uniform_discount_Riemann
    (fun t => riskProcess X x D t ω + δ) (fun t => Y (t, ω))
    a b q T hT hq.le B hB hBS hreserve' hpre' w hcont
