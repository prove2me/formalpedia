-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_source_postPayment_exponential_strictKilled_dyadic_rightMesh_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:00:30.393608+00:00
-- url     : https://prove2.me/submissions/81ae67d4-968e-4b78-8c6c-5c35c9faa2b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_exponential_dyadic_rightMesh_tendsto
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
    (hT : 0 < T) (hs : s ≤ T) (τ : ℝ≥0∞) :
    Tendsto
      (fun n : ℕ =>
        let k := Nat.ceil (((s / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
        let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
        if (u : ℝ≥0∞) < τ then
          Real.exp (θ * (x + X.X u ω - rightLimit D u ω) -
            (u : ℝ) * q) else 0) atTop
      (𝓝 (if (s : ℝ≥0∞) < τ then
        Real.exp (θ * (x + X.X s ω - rightLimit D s ω) -
          (s : ℝ) * q) else 0)) := by
  let r : ℝ≥0 := s / T
  let k : ℕ → ℕ := fun n => Nat.ceil ((r : ℝ) * (2 : ℝ) ^ n)
  let u : ℕ → ℝ≥0 := fun n =>
    (k n : ℝ≥0) / (2 : ℝ≥0) ^ n * T
  have hgrid := avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit
    s T hT hs
  have hsrc : Tendsto
      (fun n : ℕ => Real.exp
        (θ * (x + X.X (u n) ω - rightLimit D (u n) ω) -
          (u n : ℝ) * q)) atTop
      (𝓝 (Real.exp (θ * (x + X.X s ω - rightLimit D s ω) -
        (s : ℝ) * q))) := by
    simpa only [u, k, r] using
      (avram_wave4_03_source_postPayment_exponential_dyadic_rightMesh_tendsto
        X x D hD θ q ω s T hT hs)
  have hcoelim : Tendsto (fun n : ℕ => (u n : ℝ≥0∞)) atTop
      (𝓝 (s : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto s).comp hgrid.2
  change Tendsto
    (fun n : ℕ => if (u n : ℝ≥0∞) < τ then
      Real.exp (θ * (x + X.X (u n) ω - rightLimit D (u n) ω) -
        (u n : ℝ) * q) else 0) atTop
    (𝓝 (if (s : ℝ≥0∞) < τ then
      Real.exp (θ * (x + X.X s ω - rightLimit D s ω) -
        (s : ℝ) * q) else 0))
  by_cases hbefore : (s : ℝ≥0∞) < τ
  · have hev : ∀ᶠ n : ℕ in atTop, (u n : ℝ≥0∞) < τ :=
      hcoelim.eventually (isOpen_Iio.mem_nhds hbefore)
    have heq : (fun n : ℕ => if (u n : ℝ≥0∞) < τ then
        Real.exp (θ * (x + X.X (u n) ω - rightLimit D (u n) ω) -
          (u n : ℝ) * q) else 0) =ᶠ[atTop]
        (fun n : ℕ => Real.exp
          (θ * (x + X.X (u n) ω - rightLimit D (u n) ω) -
            (u n : ℝ) * q)) := by
      filter_upwards [hev] with n hn
      simp [hn]
    simpa only [if_pos hbefore] using Tendsto.congr' heq.symm hsrc
  · have hnot (n : ℕ) : ¬ (u n : ℝ≥0∞) < τ := by
      have hsle : (s : ℝ≥0∞) ≤ (u n : ℝ≥0∞) := by
        exact ENNReal.coe_le_coe.mpr (hgrid.1 n).1
      exact fun h => hbefore (lt_of_le_of_lt hsle h)
    have hzero : (fun n : ℕ => if (u n : ℝ≥0∞) < τ then
        Real.exp (θ * (x + X.X (u n) ω - rightLimit D (u n) ω) -
          (u n : ℝ) * q) else 0) = (fun _ : ℕ => (0 : ℝ)) := by
      funext n
      simp [hnot n]
    rw [hzero, if_neg hbefore]
    exact tendsto_const_nhds
