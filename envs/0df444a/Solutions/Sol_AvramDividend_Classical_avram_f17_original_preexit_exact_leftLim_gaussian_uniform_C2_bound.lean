-- Prove2me | solution 1 for AvramDividend.Classical.avram_f17_original_preexit_exact_leftLim_gaussian_uniform_C2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:40:58.264176+00:00
-- url     : https://prove2.me/submissions/55ccf0a5-f0e8-4fca-aa90-31074987c9a2

import Mathlib
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.DenselyOrdered
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_leftlimit_gaussian_uniform_C2_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
              upper < x + X.X (r k) ω - rightLimit D (r k) ω
          then (r k : WithTop ℝ≥0) else ⊤) →
        ∀ t : ℝ≥0, 0 < t → t < T →
          let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
          y ∈ Set.Icc lower upper ∧
            |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG ∧
            |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ KH := by
  classical
  obtain ⟨KG, KH, hKG, hKH, hsource⟩ :=
    avram_f17_original_preexit_leftlimit_gaussian_uniform_C2_bound
      X hBV hν q hq C w hw x D hD r lower upper hlower hcap hgrid
  refine ⟨KG, KH, hKG, hKH, ?_⟩
  intro ω T hclock t ht htT
  obtain ⟨l, hl, hband, hgrad, hhess⟩ :=
    hsource ω T hclock t ht htT
  haveI : (𝓝[<] t).NeBot :=
    nhdsWithin_Iio_neBot' ⟨0, ht⟩ le_rfl
  have hEq : Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t = l :=
    leftLim_eq_of_tendsto hl
  simpa only [hEq] using And.intro hband (And.intro hgrad hhess)
