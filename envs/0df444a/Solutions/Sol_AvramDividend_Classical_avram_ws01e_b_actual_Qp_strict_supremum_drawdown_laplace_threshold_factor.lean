-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_Qp_strict_supremum_drawdown_laplace_threshold_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:07:52.609891+00:00
-- url     : https://prove2.me/submissions/7272a6d9-b9a0-49e6-affb-668c393928d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_regenerative_reward_event_factor
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_countable_drawdown_test_measurable_fresh_shifted
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_real_clock_firstRecord_H_drawdown_reset
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_weak_record_to_strict_supremum_reward_factor
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (b β : ℝ) (hb : 0 ≤ b) (hβ : 0 < β) :
    (let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal
         (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
           (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let S : Ω × ℝ → ℝ := fun z => runningSup X (Real.toNNReal z.2) z.1
     let D : Ω × ℝ → ℝ := fun z => S z - X.X (Real.toNNReal z.2) z.1
     (∫⁻ z in {z : Ω × ℝ | b < S z},
       ENNReal.ofReal (Real.exp (-β * D z)) ∂Qp) =
     Qp {z : Ω × ℝ | b < S z} *
       (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp (-β * D z)) ∂Qp)) := by
  classical
  let S : Ω × ℝ → ℝ := fun z => runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ := fun z => S z - X.X (Real.toNNReal z.2) z.1
  let W : Ω × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (-β * D z))
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun t f =>
    Filter.limsup (fun n : ℕ =>
      let r : ℝ≥0 := (Nat.ceil ((t : ℝ) * (2 : ℝ)^n) : ℝ≥0) / (2 : ℝ≥0)^n
      ENNReal.ofReal (Real.exp (-β * ((⨆ i : ℕ, if samples i ≤ r then
        ENNReal.ofReal (f (samples i)) else 0).toReal - f r)))) Filter.atTop
  have hTest := avram_ws01e_b_actual_countable_drawdown_test_measurable_fresh_shifted X β
  change Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2) ∧
    (∀ (ω : Ω) (t : ℝ≥0), H t (fun s : ℝ≥0 => X.X s ω) =
      ENNReal.ofReal (Real.exp (-β * (runningSup X t ω - X.X t ω)))) ∧
    (∀ (ω : Ω) (u t : ℝ≥0), H t (fun s : ℝ≥0 => X.X (u + s) ω - X.X u ω) =
      ENNReal.ofReal (Real.exp (-β * (sSup ((fun v : ℝ≥0 =>
        X.X (u + v) ω - X.X u ω) '' Set.Icc 0 t) -
        (X.X (u + t) ω - X.X u ω))))) at hTest
  rcases hTest with ⟨hH, hFresh, hShift⟩
  have hW : Measurable W := by
    have hDMeas : Measurable D := by
      simpa only [D, S] using (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul hDMeas))
  have hFreshW (ω : Ω) (r : ℝ) :
      W (ω, r) = H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) :=
    (hFresh ω (Real.toNNReal r)).symm
  have hResetW (z : Ω × ℝ)
      (hFinite : twoSidedExitUpTime X b z.1 < ⊤)
      (hObs : ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2) :
      W z = H (Real.toNNReal (z.2 -
        ((twoSidedExitUpTime X b z.1).toNNReal : ℝ)))
        (fun s : ℝ≥0 =>
          X.X ((twoSidedExitUpTime X b z.1).toNNReal + s) z.1 -
            X.X (twoSidedExitUpTime X b z.1).toNNReal z.1) :=
    (avram_ws01e_b_actual_real_clock_firstRecord_H_drawdown_reset
      X b hb β H hShift z hFinite hObs).symm
  have hWeak := avram_ws01e_b_actual_Qp_regenerative_reward_event_factor
    X b hb θ p hθ hp hJoint W hW H hH hFreshW hResetW
  have hStrict := avram_ws01e_b_actual_Qp_weak_record_to_strict_supremum_reward_factor
    X θ p hθ hp b hb W hWeak
  simpa only [W, D, S] using hStrict
