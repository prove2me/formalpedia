-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18p1b_fatou_large_negative_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T02:00:05.571185+00:00
-- url     : https://prove2.me/submissions/c7d7c1ac-7625-4dea-9ae0-82062db3f615

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Fatou's lemma for negative-tail exponential difference quotients. -/
theorem solution
    (ν : Measure ℝ) (D : ℝ)
    (hBound : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      (∫⁻ z in Iic (-1 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (θ * z)) / θ) ∂ν) ≤
        ENNReal.ofReal D) :
    (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂ν) < ⊤ := by
  let θ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hθPos (n : ℕ) : 0 < θ n := by
    dsimp [θ]
    positivity
  have hθLe (n : ℕ) : θ n ≤ 1 := by
    dsimp [θ]
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact (div_le_iff₀ (by positivity)).2 (by simpa using hn)
  have hθLimit : Tendsto θ atTop (nhds (0 : ℝ)) := by
    simpa only [θ] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hθPunct : Tendsto θ atTop (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hθLimit, ?_⟩
    filter_upwards [] with n
    simp only [mem_compl_iff, mem_singleton_iff]
    exact (hθPos n).ne'
  let f : ℕ → ℝ → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal ((1 - Real.exp (θ n * z)) / θ n)
  have hfMeas (n : ℕ) : Measurable (f n) := by
    dsimp [f]
    fun_prop
  have hfLimit (z : ℝ) :
      Tendsto (fun n => f n z) atTop (nhds (ENNReal.ofReal (-z))) := by
    have hLinear : HasDerivAt (fun u : ℝ => u * z) z 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const z
    have hExp : HasDerivAt (fun u : ℝ => Real.exp (u * z)) z 0 := by
      convert (Real.hasDerivAt_exp (0 * z)).comp 0 hLinear using 1 <;>
        first | rfl | simp [Function.comp_def, mul_comm]
    have hSlope := hExp.tendsto_slope_zero
    have hReal : Tendsto (fun n =>
        (1 - Real.exp (θ n * z)) / θ n) atTop (nhds (-z)) := by
      have hComp := hSlope.comp hθPunct
      have hNeg : Tendsto (fun n =>
          -((θ n)⁻¹ * (Real.exp (θ n * z) - 1))) atTop (nhds (-z)) := by
        simpa [Function.comp_def, smul_eq_mul, Real.exp_zero,
          zero_add, mul_comm] using hComp.neg
      convert hNeg using 1
      ext n
      ring
    exact (ENNReal.continuous_ofReal.tendsto (-z)).comp hReal
  have hfPoint (z : ℝ) (hz : z ∈ Iic (-1 : ℝ)) :
      Filter.liminf (fun n => f n z) atTop = ENNReal.ofReal |z| := by
    have hzNonpos : z ≤ 0 := hz.trans (by norm_num)
    simpa [abs_of_nonpos hzNonpos] using (hfLimit z).liminf_eq
  have hFatou :
      (∫⁻ z in Iic (-1 : ℝ),
          Filter.liminf (fun n => f n z) atTop ∂ν) ≤
        Filter.liminf (fun n =>
          ∫⁻ z in Iic (-1 : ℝ), f n z ∂ν) atTop := by
    exact lintegral_liminf_le hfMeas
  have hRewrite :
      (∫⁻ z in Iic (-1 : ℝ),
          Filter.liminf (fun n => f n z) atTop ∂ν) =
      (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂ν) := by
    apply setLIntegral_congr_fun measurableSet_Iic
    intro z hz
    exact hfPoint z hz
  have hUpper :
      Filter.liminf (fun n => ∫⁻ z in Iic (-1 : ℝ), f n z ∂ν) atTop ≤
        ENNReal.ofReal D := by
    apply Filter.liminf_le_of_le
    · exact ⟨0, Filter.Eventually.of_forall (fun n => by exact bot_le)⟩
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (by simpa [f] using hBound (θ n) (hθPos n) (hθLe n))
  exact lt_of_le_of_lt (hRewrite.symm ▸ hFatou.trans hUpper)
    ENNReal.ofReal_lt_top
