-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_limsup_reward_measurable_fresh_shifted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T21:49:17.044071+00:00
-- url     : https://prove2.me/submissions/5d306d7e-00e2-429c-8037-85c796d9b37a

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_dyadic_ceiling_prefix_drawdown_reward_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_levy_cantor_dyadic_drawdown_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_limsup_reward_eq_true_drawdown
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (β : ℝ) :
    (let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     let H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun t f =>
       Filter.limsup (fun n : ℕ =>
         let r : ℝ≥0 :=
           (Nat.ceil ((t : ℝ) * (2 : ℝ)^n) : ℝ≥0) / (2 : ℝ≥0)^n
         ENNReal.ofReal (Real.exp
           (-β * ((⨆ i : ℕ, if samples i ≤ r then
             ENNReal.ofReal (f (samples i)) else 0).toReal - f r)))) atTop
     Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2) ∧
     (∀ (ω : Ω) (t : ℝ≥0),
       H t (fun s : ℝ≥0 => X.X s ω) =
         ENNReal.ofReal (Real.exp (-β * (runningSup X t ω - X.X t ω)))) ∧
     (∀ (ω : Ω) (u t : ℝ≥0),
       H t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω) =
         ENNReal.ofReal (Real.exp (-β *
           (sSup ((fun v : ℝ≥0 =>
             X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
             (X.X (u + t) ω - X.X u ω)))))) := by
  classical
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let reward (n : ℕ) (t : ℝ≥0) (f : ℝ≥0 → ℝ) : ℝ≥0∞ :=
    let r : ℝ≥0 :=
      (Nat.ceil ((t : ℝ) * (2 : ℝ)^n) : ℝ≥0) / (2 : ℝ≥0)^n
    ENNReal.ofReal (Real.exp
      (-β * ((⨆ i : ℕ, if samples i ≤ r then
        ENNReal.ofReal (f (samples i)) else 0).toReal - f r)))
  let H (t : ℝ≥0) (f : ℝ≥0 → ℝ) : ℝ≥0∞ :=
    Filter.limsup (fun n : ℕ => reward n t f) atTop
  have hReward (n : ℕ) :
      Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => reward n z.1 z.2) := by
    simpa only [reward] using
      (avram_ws01e_b_dyadic_ceiling_prefix_drawdown_reward_joint_measurable
        samples β n)
  have hMeas :
      Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2) :=
    Measurable.limsup hReward
  have hFresh (ω : Ω) (t : ℝ≥0) :
      H t (fun s : ℝ≥0 => X.X s ω) =
        ENNReal.ofReal (Real.exp (-β * (runningSup X t ω - X.X t ω))) := by
    let d : ℕ → ℝ := fun n =>
      let r : ℝ≥0 :=
        (Nat.ceil ((t : ℝ) * (2 : ℝ)^n) : ℝ≥0) / (2 : ℝ≥0)^n
      (⨆ i : ℕ, if samples i ≤ r then
        ENNReal.ofReal (X.X (samples i) ω) else 0).toReal - X.X r ω
    let dLimit : ℝ := runningSup X t ω - X.X t ω
    have hD : Tendsto d atTop (𝓝 dLimit) := by
      simpa only [d, dLimit, samples] using
        (avram_ws01e_b_actual_levy_cantor_dyadic_drawdown_tendsto X ω t)
    have hCont : Continuous (fun x : ℝ =>
        ENNReal.ofReal (Real.exp (-β * x))) :=
      ENNReal.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hF : Tendsto (fun n : ℕ =>
        ENNReal.ofReal (Real.exp (-β * d n))) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-β * dLimit)))) :=
      (hCont.tendsto dLimit).comp hD
    change Filter.limsup (fun n : ℕ =>
      ENNReal.ofReal (Real.exp (-β * d n))) atTop =
      ENNReal.ofReal (Real.exp (-β * dLimit))
    exact hF.limsup_eq
  have hShift (ω : Ω) (u t : ℝ≥0) :
      H t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω) =
        ENNReal.ofReal (Real.exp (-β *
          (sSup ((fun v : ℝ≥0 =>
            X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
            (X.X (u + t) ω - X.X u ω)))) := by
    have htail (k : ℕ) :
        (⨆ n : ℕ, if k ≤ n then
          reward n t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω) else 0) =
        (⨆ n : ℕ, ⨆ (_ : k ≤ n),
          reward n t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω)) := by
      rw [iSup_ite]
      simp
    have hOld :
        H t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω) =
          (⨅ k : ℕ, ⨆ n : ℕ, if k ≤ n then
            reward n t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω)
          else 0) := by
      dsimp [H]
      rw [Filter.limsup_eq_iInf_iSup_of_nat]
      simp_rw [htail]
    rw [hOld]
    simpa only [reward, samples] using
      (avram_ws01e_b_actual_shifted_levy_limsup_reward_eq_true_drawdown
        X ω u t β)
  exact ⟨hMeas, hFresh, hShift⟩
