-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_source_esscher_flatness_to_record_hazard_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:22:17.057864+00:00
-- url     : https://prove2.me/submissions/82b77fd3-1828-46c9-98a8-92bdbdd1b16f

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_esscher_record_log_derivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- Transfers the actual strict-record Esscher log derivative to its hazard. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x)
    (hflat : Tendsto
      (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x)
      atTop (nhds (0 : ℝ))) :
    Tendsto
      (fun a : ℝ => -Real.log
        ((∫⁻ ω, if twoSidedExitUpTime X 1 ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
          else 0 ∂P).toReal))
      atTop (nhds φ) := by
  let K : ℝ → ℝ := fun a => -Real.log ((∫⁻ ω,
    if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  have hD : ∀ x : ℝ, 0 < x →
      deriv (fun z : ℝ => Real.log (V z)) x = K x - φ := by
    intro x hx
    exact (avram_wave4_02_source_esscher_record_log_derivative
      X q hq W hW hvar φ hφ hroot V hV x hx).deriv
  have hsum : Tendsto
      (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x + φ)
      atTop (nhds φ) := by
    simpa only [zero_add] using hflat.add tendsto_const_nhds
  have hident : K =ᶠ[atTop]
      (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x + φ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [hD x hx]
    dsimp only [K]
    ring
  change Tendsto K atTop (nhds φ)
  exact hsum.congr' hident.symm
