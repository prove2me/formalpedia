-- Prove2me | solution 1 for AvramDividend.Classical.levy_positive_root_uniform_grid_upcrossing_discount_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:30:22.172094+00:00
-- url     : https://prove2.me/submissions/2d722609-ae2d-4c1c-b91b-4e95848aad4b

import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration
import Theorems.Thm_AvramDividend_Classical_levy_one_sided_capped_grid_upper_exit_discount_bound
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_discount_integrable
import Theorems.Thm_AvramDividend_Classical_capped_discrete_upcrossing_payoff_tendsto
import Theorems.Thm_AvramDividend_Classical_grid_exit_real_to_lintegral_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (h : ℝ≥0) (hh : 0 < h) :
    (∫⁻ ω : Ω,
      let up := ⨅ k : ℕ,
        if z < X.X ((k : ℝ≥0) * h) ω then
          (((k : ℝ≥0) * h) : ℝ≥0∞) else ∞
      if up < (⊤ : ℝ≥0∞) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal up)))
      else 0 ∂P) ≤ ENNReal.ofReal (Real.exp (-(φ * z))) := by
  classical
  let clock : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * h
  have hc : Monotone clock := by
    intro i j hij
    change (i : ℝ≥0) * h ≤ (j : ℝ≥0) * h
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have hc0 : clock 0 = 0 := by simp [clock]
  obtain ⟨H, hH⟩ := chat03_monotone_clock_reindexed_filtration 𝓕 clock hc
  let K : ℕ → Ω → ℕ := fun m ω =>
    hittingBtwn (fun k ω' => X.X (clock k) ω') (Ioi z) 0 m ω
  let f : ℕ → Ω → ℝ := fun m =>
    {ω : Ω | z < X.X (clock (K m ω)) ω}.indicator
      (fun ω => Real.exp (-((clock (K m ω) : ℝ) * q)))
  let T : Ω → ℝ≥0∞ := fun ω =>
    ⨅ k : ℕ, if z < X.X (clock k) ω then
      (clock k : ℝ≥0∞) else ∞
  let F : Ω → ℝ≥0∞ := fun ω =>
    if T ω < ∞ then ENNReal.ofReal
      (Real.exp (-(q * ENNReal.toReal (T ω)))) else 0
  have hK (m : ℕ) (ω : Ω) : K m ω =
      hittingBtwn (fun k ω' => X.X (clock k) ω' - z)
        (Ioi (0 : ℝ)) 0 m ω := by
    dsimp [K]
    simp [hittingBtwn_def, mem_Ioi, sub_pos]
  have hMeas (m : ℕ) : Measurable (f m) := by
    have hm := levy_upper_grid_stopped_reserve_time_measurable
      X clock H hH z m (K m) (by intro ω; rfl)
    have hs : MeasurableSet {ω : Ω | z < X.X (clock (K m ω)) ω} :=
      measurableSet_Ioi.preimage hm.1
    have he : Measurable (fun ω : Ω =>
        Real.exp (-((clock (K m ω) : ℝ) * q))) :=
      Real.measurable_exp.comp ((hm.2.mul_const q).neg)
    exact he.indicator hs
  have hInt (m : ℕ) : Integrable (f m) P := by
    simpa only [f, neg_mul] using
      (levy_upper_grid_discount_integrable
        X clock H hH z m (K m) (by intro ω; rfl) q (le_of_lt hq))
  have hPos (m : ℕ) (ω : Ω) : 0 ≤ f m ω := by
    by_cases hw : z < X.X (clock (K m ω)) ω
    · change 0 ≤ ({ω : Ω | z < X.X (clock (K m ω)) ω}.indicator
          (fun ω => Real.exp (-((clock (K m ω) : ℝ) * q))) ω)
      rw [Set.indicator_of_mem (show ω ∈ {ω : Ω | z < X.X (clock (K m ω)) ω} from hw)]
      exact le_of_lt (Real.exp_pos _)
    · simp [f, Set.indicator, hw]
  have hBound (m : ℕ) : (∫ ω, f m ω ∂P) ≤
      Real.exp (-(φ * z)) := by
    have hb := levy_one_sided_capped_grid_upper_exit_discount_bound
      X clock hc hc0 H hH φ (le_of_lt hφ)
      (by rw [hroot]; exact le_of_lt hq)
      z m (K m) (hK m)
    rw [hroot] at hb
    simpa only [f, neg_mul] using hb
  have hLimit (ω : Ω) :
      F ω ≤ liminf (fun m => ENNReal.ofReal (f m ω)) atTop := by
    have hp := capped_discrete_upcrossing_payoff_tendsto
      (fun k => X.X (clock k) ω) clock hc z q
    have hEqK (m : ℕ) :
        hittingBtwn (fun k (_ : Unit) => X.X (clock k) ω)
          (Ioi z) 0 m () = K m ω := by
      rfl
    have ht : Tendsto (fun m => ENNReal.ofReal (f m ω))
        atTop (𝓝 (F ω)) := by
      convert hp using 1
      · funext m
        rw [hEqK m]
        by_cases hw : z < X.X (clock (K m ω)) ω
        · simp [f, Set.indicator, hw, mul_comm]
        · simp [f, Set.indicator, hw]
    rw [Filter.Tendsto.liminf_eq ht]
  change (∫⁻ ω, F ω ∂P) ≤ ENNReal.ofReal (Real.exp (-(φ * z)))
  exact grid_exit_real_to_lintegral_limit P F f
    (Real.exp (-(φ * z))) hMeas hInt hPos hLimit hBound
