-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_tendsto_zero_record_height
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:34:42.120852+00:00
-- url     : https://prove2.me/submissions/b0126f28-e81b-462d-99bd-3664d7003cd5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_pos_le_root_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- The genuine killed original-record height discount has zero tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun h : ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X a ω then
            ENNReal.ofReal
              (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)
      atTop (nhds (0 : ℝ)) := by
  let G : ℝ → ℝ := fun h =>
    (∫⁻ ω, if twoSidedExitUpTime X h ω < barrierRuinTime X a ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X h ω).toReal)))
    else 0 ∂P).toReal
  have hscale : Tendsto (fun h : ℝ => φ * h) atTop atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos hφ).2 tendsto_id
  have hExp : Tendsto (fun h : ℝ => Real.exp (-(φ * h)))
      atTop (nhds (0 : ℝ)) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hbounds : ∀ᶠ h : ℝ in atTop,
      0 ≤ G h ∧ G h ≤ Real.exp (-(φ * h)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with h hh
    obtain ⟨hpos, hle⟩ :=
      avram_wave4_01_original_record_discount_pos_le_root_bound
        X q hq W hW hvar φ hφ hroot a h ha hh
    exact ⟨le_of_lt hpos, hle⟩
  change Tendsto G atTop (nhds (0 : ℝ))
  exact squeeze_zero'
    (hbounds.mono (fun h hh => hh.1))
    (hbounds.mono (fun h hh => hh.2)) hExp
