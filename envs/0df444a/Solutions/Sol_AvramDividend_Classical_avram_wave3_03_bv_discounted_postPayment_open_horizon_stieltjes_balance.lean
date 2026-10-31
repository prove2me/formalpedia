-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_open_horizon_stieltjes_balance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:05:39.835987+00:00
-- url     : https://prove2.me/submissions/2e67e44e-530b-4e0c-848d-26226c58588e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_zero_stieltjes_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_closed_horizon_stieltjes_balance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Excluding the initial time preserves the exact discounted test-value
    balance because the post-payment Stieltjes process has no zero atom. -/
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
        hg.vectorMeasure (Ioc 0 T) = g T - g 0 := by
  filter_upwards [
    avram_wave3_03_bv_discounted_postPayment_closed_horizon_stieltjes_balance
      X hX hBV x D hD q hq v L hv,
    avram_wave3_03_bv_discounted_postPayment_zero_stieltjes_atom
      X hX hBV x D hD q hq v L hv
  ] with ω hclosed hzero
  intro T
  rcases hclosed T with ⟨hg, hIcc⟩
  rcases hzero T with ⟨hz, hz0⟩
  let g : ℝ≥0 → ℝ := fun t => Real.exp (-q * (t : ℝ)) *
    v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
  change ∃ hg : BoundedVariationOn g Set.univ,
    hg.vectorMeasure (Ioc 0 T) = g T - g 0
  have hzero' : hg.vectorMeasure ({0} : Set ℝ≥0) = 0 := hz0
  have h0T : (0 : ℝ≥0) ≤ T := by positivity
  have hsplit : hg.vectorMeasure (Icc 0 T) =
      hg.vectorMeasure ({0} : Set ℝ≥0) + hg.vectorMeasure (Ioc 0 T) := by
    calc
      hg.vectorMeasure (Icc 0 T) =
          hg.vectorMeasure (Icc 0 0) + hg.vectorMeasure (Ioc 0 T) := by
            rw [← Icc_union_Ioc_eq_Icc le_rfl h0T,
              VectorMeasure.of_union (by simp) measurableSet_Icc measurableSet_Ioc]
      _ = hg.vectorMeasure ({0} : Set ℝ≥0) +
            hg.vectorMeasure (Ioc 0 T) := by simp only [Icc_self]
  refine ⟨hg, ?_⟩
  rw [hIcc, hzero'] at hsplit
  simpa only [zero_add] using hsplit.symm
