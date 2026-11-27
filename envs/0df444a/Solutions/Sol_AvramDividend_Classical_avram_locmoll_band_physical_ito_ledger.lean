-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_physical_ito_ledger
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:14:54.351743+00:00
-- url     : https://prove2.me/submissions/87df7645-127a-472d-86fe-536d5d044c1c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_exact_ito_identity
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_diffuse_sign
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_atom_endpoint_bound
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
    ∃ M : Ω → ℝ, Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      ∀ᵐ ω ∂P, Term ω + Cash ω ≤ g x + δ + M ω + G ω := by 
  classical
  dsimp only
  obtain ⟨M, hMI, hM0, hEq⟩ := avram_locmoll_band_exact_ito_identity X hX hBV q hq C hC x hx hxc D hD T hT δ R hδ hδx hxR θ hθle hprefix hstop g hg hNonneg hZero hGrad hGen hSec hLoss
  refine ⟨M, hMI, hM0, ?_⟩
  filter_upwards [hEq] with ω hw
  obtain ⟨hsum, he⟩ := hw
  have hDsign := avram_locmoll_band_diffuse_sign X hX hBV q hq C hC x hx hxc D hD T hT δ R hδ hδx hxR θ hθle hprefix hstop g hg hNonneg hZero hGrad hGen hSec hLoss ω
  have hJsign := avram_locmoll_band_atom_endpoint_bound X hX hBV q hq C hC x hx hxc D hD T hT δ R hδ hδx hxR θ hθle hprefix hstop g hg hNonneg hZero hGrad hGen hSec hLoss ω
  have hsingle : Summable (fun s : ℝ≥0 => if s = θ ω then δ else 0) :=
    summable_of_ne_finset_zero (s := {θ ω}) (fun s hs => if_neg (by simpa using hs))
  have hbound := hsum.tsum_le_tsum hJsign hsingle
  have hsingle_sum : (∑' s : ℝ≥0, if s = θ ω then δ else 0) = δ :=
    (tsum_eq_single (θ ω) (fun s hs => if_neg hs)).trans (if_pos rfl)
  rw [hsingle_sum] at hbound
  linarith
