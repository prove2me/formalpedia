-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_tendsto_one_small_height
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:53:08.291776+00:00
-- url     : https://prove2.me/submissions/4740b586-42b2-45ea-a1dc-e2737a4c5ee1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_exponential_hazard
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- The genuine killed strict-record kernel normalizes to one at height zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun h : ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (1 : ℝ)) := by
  let K : ℝ := -Real.log ((∫⁻ ω,
    if twoSidedExitUpTime X 1 ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
    else 0 ∂P).toReal)
  let G : ℝ → ℝ := fun h =>
    (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P).toReal
  have hcont : ContinuousAt (fun h : ℝ => Real.exp (-(h * K))) 0 := by
    fun_prop
  have hexp : Tendsto (fun h : ℝ => Real.exp (-(h * K)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (1 : ℝ)) := by
    have h0 : Tendsto (fun h : ℝ => Real.exp (-(h * K)))
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (Real.exp (-(0 * K)))) :=
      hcont.tendsto.mono_left
        (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds (0 : ℝ))
    simpa only [zero_mul, neg_zero, Real.exp_zero] using h0
  have heq : (fun h : ℝ => G h) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun h : ℝ => Real.exp (-(h * K))) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa only [G, K, neg_mul] using
      (avram_wave4_01_original_record_exponential_hazard
        X q hq W hW hvar a ha h hh)
  change Tendsto G (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (1 : ℝ))
  exact hexp.congr' heq.symm
