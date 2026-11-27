-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_exact_ito_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:18:37.20489+00:00
-- url     : https://prove2.me/submissions/63bb8032-d043-435a-89fc-2e252efc216e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ruin_grid_two_component_limit_assembles_ito
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_clock_le_ruin
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_uniform_grid_properties
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_grid_source_limit
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_grid_dividend_limit
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
      a - b ≤ g a - g b + δ) :
    let Cash : Ω → ℝ := (fun ω : Ω => (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (θ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
    let G : Ω → ℝ := (fun ω : Ω => ∫ t in Ioc (0 : ℝ) (θ ω : ℝ),
      Real.exp (-(q * t)) *
        (X.generator g (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal) -
          q * g (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t.toNNReal)))
    let Term : Ω → ℝ := fun ω => Real.exp (-(q * (θ ω : ℝ))) *
      g (if θ ω = 0 ∨ (θ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (θ ω) ω - rightLimit D (θ ω) ω
        else riskProcess X x D (θ ω) ω)
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
    ∃ M : Ω → ℝ, Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      ∀ᵐ ω ∂P, Summable (J ω) ∧
        Term ω + Cash ω = g x + M ω + G ω + Diff ω + ∑' s : ℝ≥0, J ω s := by 
  dsimp only
  obtain ⟨m, M, hm, hMI, hM0, hSourceLimit⟩ := avram_locmoll_band_grid_source_limit X hX hBV q hq C hC x hx hxc D hD T hT δ R hδ hδx hxR θ hθle hprefix hstop g hg hNonneg hZero hGrad hGen hSec hLoss
  have hDividend := avram_locmoll_band_grid_dividend_limit X hX hBV q hq C hC x hx hxc D hD T hT δ R hδ hδx hxR θ hθle hprefix hstop g hg hNonneg hZero hGrad hGen hSec hLoss m hm
  have hRuin := avram_locmoll_band_clock_le_ruin X x D hD.1.1 δ R hδ θ hprefix
  obtain ⟨hmono, hzero, hend⟩ := avram_locmoll_band_uniform_grid_properties T.toNNReal m
  let u : ℕ → ℕ → ℝ≥0 := fun n i => (i : ℝ≥0) * T.toNNReal / ((m n : ℝ≥0) + 1)
  let k : ℕ → ℕ := fun n => m n + 1
  have hcover : ∀ ω, ∀ᶠ n in atTop, θ ω ≤ u n (k n) :=
    fun ω => Filter.Eventually.of_forall (fun n => by
      change θ ω ≤ (fun n i : ℕ => (i : ℝ≥0) * T.toNNReal / ((m n : ℝ≥0) + 1)) n (m n + 1)
      rw [hend n]
      exact hθle ω)
  have hDlimit := hDividend.mono (fun ω h => h.2)
  have he := avram_wave6_06_original_ruin_grid_two_component_limit_assembles_ito
    X x q D hD.1.1 g θ hRuin u k hmono hzero hcover _ _ M _ _ _ _
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) hSourceLimit hDlimit
  refine ⟨M, hMI, hM0, ?_⟩
  filter_upwards [he, hDividend] with ω he hd
  exact ⟨hd.1, by simpa only [add_assoc] using he⟩
