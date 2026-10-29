-- Prove2me | solution 1 for AvramDividend.Classical.levy_tilted_clock_drawdown_zero_atom_of_infinite_jumps_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:33:29.663835+00:00
-- url     : https://prove2.me/submissions/4e76c9a5-5eaa-4063-93e2-d23741b95359

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_genuine_descending_factor_tendsto_zero_ws01f
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (q φ p lam m : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    ((P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (φ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ φ))))
      {z : Ω × ℝ | runningSup X z.2.toNNReal z.1 -
        X.X z.2.toNNReal z.1 = 0} = 0 := by
  let μ : Measure (Ω × ℝ) :=
    (P.prod (expMeasure p)).withDensity
      (fun z => ENNReal.ofReal
        (Real.exp (φ * X.X z.2.toNNReal z.1 -
          (z.2.toNNReal : ℝ) * X.ψ φ)))
  let D : Ω × ℝ → ℝ := fun z =>
    runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1
  have hPair : Measurable (fun z : Ω × ℝ => (z.2.toNNReal, z.1)) := by fun_prop
  have hD : Measurable D :=
    ((levy_runningSup_joint_time_path_measurable X).comp hPair).sub
      ((chat04_levy_joint_time_state_measurable X).comp hPair)
  have hs : MeasurableSet {z : Ω × ℝ | D z = 0} := hD (measurableSet_singleton 0)
  have hReal : Tendsto (fun β : ℝ =>
      (p / lam) * ((lam - β) / (p - (X.ψ (φ + β) - q))))
      atTop (𝓝 0) :=
    levy_genuine_descending_factor_tendsto_zero_ws01f
      X hjump φ q p lam (by linarith)
  have hIF : Tendsto (fun β : ℝ =>
      if β = lam then p / (lam * m)
      else (p / lam) * ((lam - β) /
        (p - (X.ψ (φ + β) - q)))) atTop (𝓝 0) := by
    apply hReal.congr'
    filter_upwards [Filter.eventually_gt_atTop lam] with β hβ
    simp [ne_of_gt hβ]
  have hENN : Tendsto (fun β : ℝ =>
      ENNReal.ofReal (if β = lam then p / (lam * m)
        else (p / lam) * ((lam - β) /
          (p - (X.ψ (φ + β) - q))))) atTop (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal hIF)
  have hLap : Tendsto (fun β : ℝ =>
      ∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z)) ∂μ)
      atTop (𝓝 0) := by
    apply hENN.congr'
    filter_upwards [Filter.eventually_gt_atTop 0] with β hβ
    exact (avram_ws01e_b_genuine_tilted_exponential_descending_factor_all_beta
      X q φ p lam m hq hφ hroot hp hlam hlamroot hm hmderiv hJoint β hβ).symm
  have hBound (β : ℝ) : μ {z | D z = 0} ≤ (∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z)) ∂μ) := by
    calc
      μ {z | D z = 0} =
          ∫⁻ z, ({z | D z = 0}.indicator (fun _ => (1 : ENNReal))) z ∂μ := by
            simp [lintegral_indicator hs]
      _ ≤ ∫⁻ z, ENNReal.ofReal (Real.exp (-β * D z)) ∂μ := by
          apply lintegral_mono
          intro z
          by_cases hz : D z = 0
          · simp [Set.indicator_of_mem hz, hz]
          · rw [Set.indicator_of_notMem (show z ∉ {w | D w = 0} from hz)]
            exact bot_le
  have hZero : μ {z | D z = 0} ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hLap (Filter.Eventually.of_forall hBound)
  exact le_antisymm hZero bot_le
