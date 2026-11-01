-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_source_postPayment_exponential_dyadic_rightMesh_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:38:14.623858+00:00
-- url     : https://prove2.me/submissions/3338e7d3-aa9f-447d-96cf-a61430b8674e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (ω : Ω) (s T : ℝ≥0)
    (hT : 0 < T) (hs : s ≤ T) :
    Tendsto
      (fun n : ℕ =>
        let k := Nat.ceil (((s / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
        let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
        Real.exp (θ * (x + X.X u ω - rightLimit D u ω) -
          (u : ℝ) * q)) atTop
      (𝓝 (Real.exp (θ * (x + X.X s ω - rightLimit D s ω) -
        (s : ℝ) * q))) := by
  let r : ℝ≥0 := s / T
  let k : ℕ → ℕ := fun n => Nat.ceil ((r : ℝ) * (2 : ℝ) ^ n)
  let u : ℕ → ℝ≥0 := fun n =>
    (k n : ℝ≥0) / (2 : ℝ≥0) ^ n * T
  have hgrid := avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit
    s T hT hs
  have hwithin : Tendsto u atTop (𝓝[Ici s] s) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hgrid.2, ?_⟩
    exact Filter.Eventually.of_forall (fun n => (hgrid.1 n).1)
  have hres : ContinuousWithinAt
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
      (Ici s) s :=
    (postPaymentReserve_cadlag_adapted X x D hD).1 ω s
  have htime : ContinuousWithinAt
      (fun t : ℝ≥0 => (t : ℝ) * q) (Ici s) s :=
    (NNReal.continuous_coe.mul continuous_const).continuousWithinAt
  have harg : ContinuousWithinAt
      (fun t : ℝ≥0 =>
        θ * (x + X.X t ω - rightLimit D t ω) - (t : ℝ) * q)
      (Ici s) s := (hres.const_mul θ).sub htime
  have hvalue : ContinuousWithinAt
      (fun t : ℝ≥0 => Real.exp
        (θ * (x + X.X t ω - rightLimit D t ω) - (t : ℝ) * q))
      (Ici s) s :=
    Real.continuous_exp.continuousAt.comp_continuousWithinAt harg
  exact hvalue.tendsto.comp hwithin
