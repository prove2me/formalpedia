-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_Stieltjes_interval_mass_of_rightlimits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:47:06.594945+00:00
-- url     : https://prove2.me/submissions/0a0bc165-642a-46eb-ad6e-8ea4cb7a8d0f

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0)
    (hRight0 : Function.rightLim
      (fun z : ℝ => D z.toNNReal ω) 0 = 0)
    (hRightt : Function.rightLim
      (fun z : ℝ => D z.toNNReal ω) (t : ℝ) = (t : ℝ)) :
    dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ)) =
      ENNReal.ofReal (t : ℝ) := by
  have hMon : Monotone (fun z : ℝ => D z.toNNReal ω) :=
    (hD.2.1 ω).comp (fun a b hab => Real.toNNReal_mono hab)
  change (if hm : Monotone (fun z : ℝ => D z.toNNReal ω) then
      hm.stieltjesFunction.measure else 0) (Ioc (0 : ℝ) (t : ℝ)) =
      ENNReal.ofReal (t : ℝ)
  rw [dif_pos hMon, StieltjesFunction.measure_Ioc]
  rw [Monotone.stieltjesFunction_eq hMon,
    Monotone.stieltjesFunction_eq hMon]
  rw [hRightt, hRight0]
  simp
