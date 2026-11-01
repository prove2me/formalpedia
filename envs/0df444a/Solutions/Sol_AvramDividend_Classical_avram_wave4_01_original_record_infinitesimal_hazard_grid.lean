-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_infinitesimal_hazard_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:04:40.60329+00:00
-- url     : https://prove2.me/submissions/b6fc79d6-9e84-4576-bbbd-c88487b1c366

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
import Theorems.Thm_AvramDividend_Classical_bv_rare_grid_exponential_limit_ws01b

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The genuine source first-record discount recovers the ordinary
logarithmic q-scale killing rate from vanishing strict-record heights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤) :
    ∀ a : ℝ, 0 < a →
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) *
            (1 - (∫⁻ ω,
              if twoSidedExitUpTime X (1 / (n : ℝ)) ω <
                  barrierRuinTime X a ω then
                ENNReal.ofReal
                  (Real.exp (-(q *
                    (twoSidedExitUpTime X (1 / (n : ℝ)) ω).toReal)))
              else 0 ∂P).toReal))
        atTop (nhds (deriv W a / W a)) := by
  intro a ha
  let r : ℝ := deriv W a / W a
  let G : ℝ → ℝ := fun b =>
    (∫⁻ ω,
      if twoSidedExitUpTime X b ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X b ω).toReal)))
      else 0 ∂P).toReal
  change Tendsto
    (fun n : ℕ => (n : ℝ) * (1 - G (1 / (n : ℝ))))
    atTop (nhds r)
  have hlim :
      Tendsto (fun n : ℕ =>
        (n : ℝ) * (1 - Real.exp (-(r / (n : ℝ)))))
        atTop (nhds r) :=
    bv_rare_grid_exponential_limit_ws01b r
  have hEq :
      (fun n : ℕ => (n : ℝ) * (1 - G (1 / (n : ℝ)))) =ᶠ[atTop]
      (fun n : ℕ =>
        (n : ℝ) * (1 - Real.exp (-(r / (n : ℝ))))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    have hb : 0 < (1 / (n : ℝ)) := one_div_pos.mpr hnR
    have hG : G (1 / (n : ℝ)) =
        Real.exp (-((1 / (n : ℝ)) * r)) := by
      simpa only [G, r] using
        (avram_wave4_01_original_record_discount_exp_log_scale_deriv
          X q hq W hW hvar a (1 / (n : ℝ)) ha hb)
    have hr : (1 / (n : ℝ)) * r = r / (n : ℝ) := by
      ring
    rw [hG, hr]
  exact hlim.congr' hEq.symm
