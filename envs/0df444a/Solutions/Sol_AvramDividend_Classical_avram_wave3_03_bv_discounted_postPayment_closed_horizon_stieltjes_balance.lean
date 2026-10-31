-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_closed_horizon_stieltjes_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:00:57.708248+00:00
-- url     : https://prove2.me/submissions/e3e1cc34-4228-4ad9-8f11-f268fbd098f6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The closed finite-horizon vector Stieltjes test balance is exactly
    the terminal discounted post-payment value minus its initial value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let g : ℝ≥0 → ℝ := fun t =>
        Real.exp (-q * (t : ℝ)) *
          v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hg : BoundedVariationOn g Set.univ,
        hg.vectorMeasure (Icc 0 T) = g T - g 0 := by
  filter_upwards [
    avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting
      X hX hBV x D hD q hq v L hv
  ] with ω hω
  intro T
  rcases hω T with ⟨hg, -⟩
  let rT : ℝ := x + X.X T ω - rightLimit D T ω
  let g : ℝ≥0 → ℝ := fun t => Real.exp (-q * (t : ℝ)) *
    v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
  change ∃ hg : BoundedVariationOn g Set.univ,
    hg.vectorMeasure (Icc 0 T) = g T - g 0
  have hdisc : ContinuousAt
      (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) T := by fun_prop
  have hconst : Tendsto
      (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ)) * v rT)
      (𝓝[>] T) (𝓝 (g T)) := by
    have hconstAt : ContinuousAt
        (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ)) * v rT) T :=
      hdisc.mul continuousAt_const
    have hgT : g T = Real.exp (-q * (T : ℝ)) * v rT := by
      simp only [g, min_self, rT]
    rw [hgT]
    exact hconstAt.tendsto.mono_left nhdsWithin_le_nhds
  have hevent : (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ)) * v rT) =ᶠ[𝓝[>] T] g := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : T < t := by simpa only [mem_Ioi] using ht
    simp only [g, rT, min_eq_right ht'.le]
  have hright : Function.rightLim g T = g T :=
    rightLim_eq_of_tendsto (Tendsto.congr' hevent hconst)
  have hleft : Function.leftLim g (0 : ℝ≥0) = g 0 :=
    leftLim_eq_of_isBot (f := g) (isBot_bot : IsBot (0 : ℝ≥0))
  refine ⟨hg, ?_⟩
  have h0T : (0 : ℝ≥0) ≤ T := by positivity
  rw [hg.vectorMeasure_Icc h0T, hright, hleft]
