-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_stieltjes_tail_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:57:28.448497+00:00
-- url     : https://prove2.me/submissions/94450230-e075-4d71-9470-39256ca30e2f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The discount keeps running after reserve freezing: the strict
    post-horizon Stieltjes mass is minus the terminal discounted value. -/
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
        hg.vectorMeasure (Ioi T) =
          -(Real.exp (-q * (T : ℝ)) *
            v (x + X.X T ω - rightLimit D T ω)) := by
  filter_upwards [
    avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting
      X hX hBV x D hD q (le_of_lt hq) v L hv
  ] with ω hω
  intro T
  rcases hω T with ⟨hg, -⟩
  let rT : ℝ := x + X.X T ω - rightLimit D T ω
  let g : ℝ≥0 → ℝ := fun t => Real.exp (-q * (t : ℝ)) *
    v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
  change ∃ hg : BoundedVariationOn g Set.univ,
    hg.vectorMeasure (Ioi T) = -(Real.exp (-q * (T : ℝ)) * v rT)
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
  have hright : Tendsto g (𝓝[>] T) (𝓝 (g T)) := by
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
      exact (htail t (le_of_lt ht)).symm
    exact Tendsto.congr' hevent hconst
  have hlim : limUnder atTop g = 0 :=
    tendsto_nhds_unique hg.tendsto_atTop_limUnder htop
  have hrightlim : Function.rightLim g T = g T :=
    rightLim_eq_of_tendsto hright
  refine ⟨hg, ?_⟩
  rw [hg.vectorMeasure_Ioi T, hlim, hrightlim]
  simp only [zero_sub, g, rT, min_self]
