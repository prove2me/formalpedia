-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_shifted_levy_limsup_reward_eq_true_drawdown
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T20:29:45.29562+00:00
-- url     : https://prove2.me/submissions/ecb1112a-b7ac-4dbb-8b35-98fe3e9bb279

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_cantor_dyadic_drawdown_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (u t : ℝ≥0) (β : ℝ) :
    (⨅ k : ℕ, ⨆ n : ℕ, if k ≤ n then
        let r : ℝ≥0 :=
          (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
        let samples : ℕ → ℝ≥0 := fun j =>
          ((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
        ENNReal.ofReal (Real.exp
          (-β * ((⨆ i : ℕ, if samples i ≤ r then
            ENNReal.ofReal (X.X (u + samples i) ω - X.X u ω) else 0).toReal -
              (X.X (u + r) ω - X.X u ω))))
      else 0) =
    ENNReal.ofReal (Real.exp (-β *
      (sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
        (X.X (u + t) ω - X.X u ω)))) := by
  let d : ℕ → ℝ := fun n =>
    let r : ℝ≥0 :=
      (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
    let samples : ℕ → ℝ≥0 := fun j =>
      ((Nat.unpair j).2 : ℝ≥0) *
        (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
    (⨆ i : ℕ, if samples i ≤ r then
      ENNReal.ofReal (X.X (u + samples i) ω - X.X u ω) else 0).toReal -
      (X.X (u + r) ω - X.X u ω)
  let D : ℝ :=
    sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
      (X.X (u + t) ω - X.X u ω)
  have hD : Tendsto d atTop (𝓝 D) := by
    simpa only [d, D] using
      avram_ws01e_b_actual_shifted_levy_cantor_dyadic_drawdown_tendsto X ω u t
  have hcontinuous : Continuous (fun x : ℝ =>
      ENNReal.ofReal (Real.exp (-β * x))) :=
    ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hF : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (Real.exp (-β * d n))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (-β * D)))) :=
    (hcontinuous.tendsto D).comp hD
  have hlim := hF.limsup_eq
  rw [Filter.limsup_eq_iInf_iSup_of_nat] at hlim
  have htail (k : ℕ) :
      (⨆ n : ℕ, if k ≤ n then
        ENNReal.ofReal (Real.exp (-β * d n)) else 0) =
      (⨆ n : ℕ, ⨆ (_ : k ≤ n),
        ENNReal.ofReal (Real.exp (-β * d n))) := by
    rw [iSup_ite]
    simp
  change (⨅ k : ℕ, ⨆ n : ℕ, if k ≤ n then
    ENNReal.ofReal (Real.exp (-β * d n)) else 0) =
    ENNReal.ofReal (Real.exp (-β * D))
  simp_rw [htail]
  exact hlim
