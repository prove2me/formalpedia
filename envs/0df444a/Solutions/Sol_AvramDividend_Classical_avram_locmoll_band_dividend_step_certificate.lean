-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_dividend_step_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:15:58.404336+00:00
-- url     : https://prove2.me/submissions/aa2b367d-b589-4c99-8b00-cb12b00b392f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_dividend_step_without_limit
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_step_pointwise_endpoints
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (C : ℝ≥0∞) (hC : 0 < C)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (δ R : ℝ) (hδ : 0 < δ) (hδx : δ < x) (hxR : x < R)
    (θ : Ω → ℝ≥0)
    (hθle : ∀ ω, θ ω ≤ T.toNNReal)
    (hprefix : ∀ ω t, t < θ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc δ R)
    (hstop : IsStoppingTime 𝓕.rightCont (fun ω => (θ ω : WithTop ℝ≥0)))
    (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (hNonneg : ∀ y : ℝ, 0 ≤ g y)
    (hZero : ∀ y : ℝ, y ≤ 0 → g y = 0)
    (hGrad : ∀ y : ℝ, δ ≤ y → 1 ≤ deriv g y)
    (hGen : ∀ y : ℝ, δ ≤ y → ENNReal.ofReal y ≤ C →
      X.GeneratorIntegrable g y ∧ X.generator g y - q * g y ≤ 0)
    (hSec : ∀ a b : ℝ, δ ≤ b → b ≤ a →
      a - b ≤ g a - g b)
    (hLoss : ∀ a b : ℝ, 0 ≤ b → b ≤ a →
      a - b ≤ g a - g b + δ)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    let Cash : Ω → ℝ := (fun ω : Ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    let u : ℕ → ℕ → ℝ≥0 := fun n i => (i : ℝ≥0) * T.toNNReal / ((m n : ℝ≥0) + 1)
    let k : ℕ → ℕ := fun n => m n + 1
    let Source : ℕ → Ω → ℝ := fun n ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (θ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      ∑ i ∈ Finset.range (k n),
        ((E (v (i + 1)) - E (v i)) * g (Y (v i)) +
          E (v (i + 1)) * (g (Z i) - g (Y (v i))))
    let Dividend : ℕ → Ω → ℝ := fun n ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (θ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let pre : Prop := θ ω = 0 ∨ (θ ω : ℝ≥0∞) < ruinTime X x D ω
      (g (x - rightLimit D 0 ω) - g x) +
        (∑ i ∈ Finset.range (k n),
          ((E (v (i + 1)) - E (v i)) * g (Y (v i)) +
            E (v (i + 1)) * (g (Z i) - g (Y (v i))) +
            E (v (i + 1)) *
              (g (riskProcess X x D (v (i + 1)) ω) - g (Z i)) +
            E (v (i + 1)) *
              (g (Y (v (i + 1))) -
                g (riskProcess X x D (v (i + 1)) ω)))) +
        (if pre then 0 else E (θ ω) *
          (g (riskProcess X x D (θ ω) ω) - g (Y (θ ω)))) -
        Source n ω
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    ∀ ω, ∃ (a b c : ℕ → ℝ → ℝ) (K : ℝ),
      let μ := (dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ))
      let A : ℝ → ℝ := fun t => riskProcess X x D t.toNNReal ω
      let B : ℝ → ℝ := fun t => x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω
      let E : ℝ → ℝ := fun t => Real.exp (-(q * t))
      let F : ℕ → ℝ → ℝ := fun n t => E t - c n t * Q (a n t) (b n t)
      (∀ n t, t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ) →
        (t = 0 → a n t = x ∧ b n t = x - rightLimit D 0 ω ∧ c n t = 1) ∧
        (0 < t → ∃ i < k n,
          let l := min (u n i) (θ ω)
          let r := min (u n (i + 1)) (θ ω)
          (l : ℝ) < t ∧ t ≤ (r : ℝ) ∧
          a n t = x + X.X r ω - rightLimit D l ω ∧
          b n t = (if r = θ ω ∧ ¬ (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D ω)
            then riskProcess X x D r ω else x + X.X r ω - rightLimit D r ω) ∧
          c n t = E (r : ℝ))) ∧
      (∀ᵐ t ∂μ, B t ≤ A t ∧ ∀ n, b n t ≤ a n t) ∧
      (∀ᵐ t ∂μ, Tendsto (fun n => a n t) atTop (𝓝 (A t)) ∧
        Tendsto (fun n => b n t) atTop (𝓝 (B t)) ∧
        Tendsto (fun n => c n t) atTop (𝓝 (E t))) ∧
      (∀ n, AEStronglyMeasurable (F n) μ) ∧
      Integrable (fun _ : ℝ => K) μ ∧
      (∀ n, ∀ᵐ t ∂μ, ‖F n t‖ ≤ K) ∧
      (∀ n, Dividend n ω + Cash ω = ∫ t, F n t ∂μ) := by 
  dsimp only
  intro ω
  obtain ⟨a,b,c,K,hs,ho,hF,hK,hbound,hgrid⟩ :=
    avram_locmoll_band_dividend_step_without_limit X hX hBV q hq C hC x hx hxc D hD T hT δ R hδ hδx hxR θ hθle hprefix hstop g hg hNonneg hZero hGrad hGen hSec hLoss m hm ω
  refine ⟨a,b,c,K,hs,ho,?_,hF,hK,hbound,hgrid⟩
  have hmeas : MeasurableSet (paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ)) :=
    (avram_p4_d_dividend_original_paymentTimes_measurableSet (ruinTime X x D ω)).inter measurableSet_Iic
  filter_upwards [ae_restrict_mem hmeas] with t ht
  have he := ht.1
  change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω) at he
  exact avram_locmoll_band_step_pointwise_endpoints X x q D hD.1.1 ω T.toNNReal (θ ω)
    m hm a b c t he.1 ht.2 he.2 (fun n => (hs n t ht).1) (fun n => (hs n t ht).2)
