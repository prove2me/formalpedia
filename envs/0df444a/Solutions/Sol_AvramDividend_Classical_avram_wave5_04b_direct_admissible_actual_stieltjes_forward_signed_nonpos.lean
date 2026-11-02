-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_direct_admissible_actual_stieltjes_forward_signed_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:20:26.956259+00:00
-- url     : https://prove2.me/submissions/2f78d82a-cf69-4992-bd1b-9ca8e98b0856

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_solvent_actual_stieltjes_forward_secant_real_signed_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- For genuinely admissible original source-X dividends, the actual real
Stieltjes signed forward-secant correction is nonpositive on the full closed
horizon, including boundary contacts and singular-continuous variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q δ : ℝ) (hδ : 0 < δ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω)
    (hIntegrable : IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
        (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)))
      (Icc (0 : ℝ) (T : ℝ)) (dividendMeasure D ω)) :
    (∫ s in Icc (0 : ℝ) (T : ℝ),
      Real.exp (-(q * s)) *
        (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ)) ∂(dividendMeasure D ω)) ≤ 0 := by
  have hSolvent : ∀ s : ℝ, s ∈ Icc (0 : ℝ) (T : ℝ) →
      0 ≤ x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hsT : s ≤ (T : ℝ) := hs.2
    have hrepr : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs0
    have hleReal : (s.toNNReal : ℝ) ≤ (T : ℝ) := by
      simpa only [hrepr] using hsT
    have hle : s.toNNReal ≤ T := by
      exact_mod_cast hleReal
    have hPreS : s.toNNReal = 0 ∨
        (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω := by
      rcases hPre with hTzero | hTlt
      · left
        apply le_antisymm
        · simpa only [hTzero] using hle
        · exact zero_le
      · right
        have hcoe : (s.toNNReal : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by
          exact_mod_cast hle
        exact lt_of_le_of_lt hcoe hTlt
    have hAdmissible : IsAdmissible X x D := hD.1
    have hCover := hAdmissible.2 ω s.toNNReal hPreS
    dsimp [riskProcess] at hCover
    linarith only [hCover]
  exact avram_wave5_04b_solvent_actual_stieltjes_forward_secant_real_signed_nonpos
    X x C hC q δ hδ w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D ω T hSolvent hIntegrable
