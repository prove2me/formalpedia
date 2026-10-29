-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_exists_measurable_fullpath_drawdown_proxy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:52:42.117729+00:00
-- url     : https://prove2.me/submissions/402d9d89-c1fc-4543-ad3b-275d1c5a393e

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_dyadic_ceiling_prefix_drawdown_reward_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_levy_cantor_dyadic_drawdown_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_limsup_reward_eq_true_drawdown
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ F : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ,
      Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => F z.1 z.2) ∧
      (∀ (ω : Ω) (t : ℝ≥0),
        F t (fun s : ℝ≥0 => X.X s ω) =
          runningSup X t ω - X.X t ω) ∧
      (∀ (ω : Ω) (u t : ℝ≥0),
        F t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω) =
          sSup ((fun v : ℝ≥0 =>
            X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
            (X.X (u + t) ω - X.X u ω)) := by
  classical
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let reward (n : ℕ) (t : ℝ≥0) (f : ℝ≥0 → ℝ) : ℝ≥0∞ :=
    let r : ℝ≥0 := (Nat.ceil ((t : ℝ) * (2 : ℝ)^n) : ℝ≥0) / (2 : ℝ≥0)^n
    ENNReal.ofReal (Real.exp
      (-(1 : ℝ) * ((⨆ i : ℕ, if samples i ≤ r then
        ENNReal.ofReal (f (samples i)) else 0).toReal - f r)))
  let H0 (t : ℝ≥0) (f : ℝ≥0 → ℝ) : ℝ≥0∞ :=
    ⨅ k : ℕ, ⨆ n : ℕ, if k ≤ n then reward n t f else 0
  have hReward (n : ℕ) :
      Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => reward n z.1 z.2) := by
    simpa only [reward] using
      (avram_ws01e_b_dyadic_ceiling_prefix_drawdown_reward_joint_measurable
        samples (1 : ℝ) n)
  have hH0 : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H0 z.1 z.2) := by
    dsimp [H0]
    refine Measurable.iInf (fun k => Measurable.iSup (fun n => ?_))
    by_cases hkn : k ≤ n
    · simpa [hkn] using hReward n
    · simpa [hkn] using (measurable_const : Measurable
        (fun _ : ℝ≥0 × (ℝ≥0 → ℝ) => (0 : ℝ≥0∞)))
  have hFresh0 (ω : Ω) (t : ℝ≥0) :
      H0 t (fun s : ℝ≥0 => X.X s ω) =
        ENNReal.ofReal (Real.exp
          (-(1 : ℝ) * (runningSup X t ω - X.X t ω))) := by
    let d : ℕ → ℝ := fun n =>
      let r : ℝ≥0 := (Nat.ceil ((t : ℝ) * (2 : ℝ)^n) : ℝ≥0) /
        (2 : ℝ≥0)^n
      (⨆ i : ℕ, if samples i ≤ r then
        ENNReal.ofReal (X.X (samples i) ω) else 0).toReal - X.X r ω
    let dLimit : ℝ := runningSup X t ω - X.X t ω
    have hD : Tendsto d atTop (𝓝 dLimit) := by
      simpa only [d, dLimit, samples] using
        (avram_ws01e_b_actual_levy_cantor_dyadic_drawdown_tendsto X ω t)
    have hCont : Continuous (fun x : ℝ =>
        ENNReal.ofReal (Real.exp (-(1 : ℝ) * x))) :=
      ENNReal.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hF : Tendsto (fun n : ℕ =>
        ENNReal.ofReal (Real.exp (-(1 : ℝ) * d n))) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-(1 : ℝ) * dLimit)))) :=
      (hCont.tendsto dLimit).comp hD
    have hlim := hF.limsup_eq
    rw [Filter.limsup_eq_iInf_iSup_of_nat] at hlim
    have htail (k : ℕ) :
        (⨆ n : ℕ, if k ≤ n then
          ENNReal.ofReal (Real.exp (-(1 : ℝ) * d n)) else 0) =
        (⨆ n : ℕ, ⨆ (_ : k ≤ n),
          ENNReal.ofReal (Real.exp (-(1 : ℝ) * d n))) := by
      rw [iSup_ite]
      simp
    change (⨅ k : ℕ, ⨆ n : ℕ, if k ≤ n then
        ENNReal.ofReal (Real.exp (-(1 : ℝ) * d n)) else 0) =
        ENNReal.ofReal (Real.exp (-(1 : ℝ) * dLimit))
    simp_rw [htail]
    exact hlim
  have hShift0 (ω : Ω) (u t : ℝ≥0) :
      H0 t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω) =
        ENNReal.ofReal (Real.exp (-(1 : ℝ) *
          (sSup ((fun v : ℝ≥0 =>
            X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
            (X.X (u + t) ω - X.X u ω)))) := by
    simpa only [H0, reward, samples] using
      (avram_ws01e_b_actual_shifted_levy_limsup_reward_eq_true_drawdown
        X ω u t (1 : ℝ))

  have hDecode (d : ℝ) :
      -Real.log ((ENNReal.ofReal (Real.exp (-(1 : ℝ) * d))).toReal) = d := by
    rw [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _)), Real.log_exp]
    ring
  refine ⟨(fun t f => -Real.log ((H0 t f).toReal)), ?_, ?_, ?_⟩
  · exact (Real.measurable_log.comp
      (ENNReal.measurable_toReal.comp hH0)).neg
  · intro ω t
    change -Real.log ((H0 t (fun s : ℝ≥0 => X.X s ω)).toReal) = _
    rw [hFresh0]
    exact hDecode _
  · intro ω u t
    change -Real.log ((H0 t
      (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω)).toReal) = _
    rw [hShift0]
    exact hDecode _
