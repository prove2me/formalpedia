-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_global_stieltjes_total
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:05:32.958956+00:00
-- url     : https://prove2.me/submissions/818cd161-f2ea-4188-b5c4-2daa8ed9a898

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_stieltjes_tail_terminal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- With positive discount, the entire frozen post-payment test Stieltjes
    mass is minus the test value after any immediate dividend at time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 < q)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let g : ℝ≥0 → ℝ := fun t =>
        Real.exp (-q * (t : ℝ)) *
          v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hg : BoundedVariationOn g Set.univ,
        hg.vectorMeasure Set.univ = -g 0 := by
  filter_upwards [
    avram_wave3_03_bv_discounted_postPayment_stieltjes_tail_terminal
      X hX hBV x D hD q hq v L hv
  ] with ω hω
  intro T
  rcases hω T with ⟨hg, -⟩
  let rT : ℝ := x + X.X T ω - rightLimit D T ω
  let g : ℝ≥0 → ℝ := fun t => Real.exp (-q * (t : ℝ)) *
    v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
  change ∃ hg : BoundedVariationOn g Set.univ,
    hg.vectorMeasure Set.univ = -g 0
  have htail (t : ℝ≥0) (ht : T ≤ t) :
      g t = Real.exp (-q * (t : ℝ)) * v rT := by
    simp only [g, rT, min_eq_right ht]
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hneg : Tendsto (fun t : ℝ≥0 => -q * (t : ℝ)) atTop atBot :=
    (tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr hq)).mpr hcoe
  have hexp : Tendsto (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ)))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hneg
  have htop : Tendsto g atTop (𝓝 (0 : ℝ)) := by
    have hevent : (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ)) * v rT) =ᶠ[atTop] g := by
      filter_upwards [eventually_ge_atTop T] with t ht
      exact (htail t ht).symm
    simpa only [zero_mul] using
      (Tendsto.congr' hevent (hexp.mul_const (v rT)))
  have hlim : limUnder atTop g = 0 :=
    tendsto_nhds_unique hg.tendsto_atTop_limUnder htop
  have hleft : Function.leftLim g (0 : ℝ≥0) = g 0 :=
    leftLim_eq_of_isBot (f := g) (isBot_bot : IsBot (0 : ℝ≥0))
  refine ⟨hg, ?_⟩
  calc
    hg.vectorMeasure Set.univ = hg.vectorMeasure (Ici (0 : ℝ≥0)) := by
      congr 1
      simp
    _ = limUnder atTop g - Function.leftLim g 0 := hg.vectorMeasure_Ici 0
    _ = -g 0 := by rw [hlim, hleft]; ring
