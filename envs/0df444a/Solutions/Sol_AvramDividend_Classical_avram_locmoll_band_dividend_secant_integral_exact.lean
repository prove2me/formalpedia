-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_dividend_secant_integral_exact
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:19:55.549569+00:00
-- url     : https://prove2.me/submissions/d5989e2e-d5da-45a4-af8c-4ac1a2a962b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_zero_drop_measurable
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_integrable
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_diffuse_integral
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_atomic_integral
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_secant_atom_product
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_eligible_prepost
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
    let J : Ω → ℝ≥0 → ℝ := fun ω s =>
      if s ≤ θ ω ∧ (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) then
        Real.exp (-(q * (s : ℝ))) *
          ((rightLimit D s ω - D s ω) +
            g (x + X.X s ω - rightLimit D s ω) - g (riskProcess X x D s ω))
      else 0
    let Diff : Ω → ℝ := fun ω =>
      ∫ t in (paymentTimes (ruinTime X x D ω) ∩ Ioc (0 : ℝ) (θ ω : ℝ)),
        Real.exp (-(q * t)) *
          (1 - deriv g (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal))
        ∂((dividendMeasure D ω).restrict
          {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω})
    let Q : ℝ → ℝ → ℝ := fun a b => if a = b then deriv g a else (g a - g b) / (a - b)
    ∀ ω,
      let μ := (dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ))
      (∫ t, Real.exp (-(q * t)) *
        (1 - Q (riskProcess X x D t.toNNReal ω)
          (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω)) ∂μ) =
        Diff ω + ∑' s : ℝ≥0, J ω s := by 
  dsimp only
  intro ω
  let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ)
  let U : Set ℝ := {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω}
  let μ := (dividendMeasure D ω).restrict S
  have hU : MeasurableSet U := avram_locmoll_band_zero_drop_measurable D hD.1.1 ω
  have hf := avram_locmoll_band_secant_integrable X x q D hD.1.1 ω (θ ω)
    g hg R hq.le (avram_locmoll_band_eligible_prepost X x C D hD δ R hxR θ hprefix ω)
  have hsplit := integral_add_compl hU hf
  have hdiff := avram_locmoll_band_secant_diffuse_integral X x q D hD.1.1 ω (θ ω) g
  have hatom := avram_locmoll_band_secant_atomic_integral X x q D hD.1.1 ω (θ ω) g hg hf
    (avram_locmoll_band_secant_atom_product X x q D hD.1.1 ω (θ ω) g)
  rw [← hsplit, hdiff, hatom]
