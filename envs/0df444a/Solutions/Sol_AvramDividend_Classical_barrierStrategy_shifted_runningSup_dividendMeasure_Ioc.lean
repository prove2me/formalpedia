-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_shifted_runningSup_dividendMeasure_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:51:04.185814+00:00
-- url     : https://prove2.me/submissions/a85d6d68-4baf-4af6-86a8-381dd80bd27c

import Theorems.Thm_AvramDividend_Classical_dividendMeasure_translated_Ioc_eq_of_increment
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_after_firstUpcrossing_increment_eq_shiftedSup
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_of_le
import Theorems.Thm_AvramDividend_Classical_shiftedSup_right_continuous_of_levy
import Theorems.Thm_AvramDividend_Classical_rightLim_comp_toNNReal_of_rightContinuous
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_monotone_of_le
import Theorems.Thm_AvramDividend_Classical_intervalSup_monotone_of_bddAbove
import Mathlib.Data.NNReal.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Shifted running-supremum dividend measures agree after the first strict barrier upcrossing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞))) :
    ∀ t : ℝ≥0,
      BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 (u + t)) →
      (dividendMeasure (barrierStrategy X x a) ω)
          (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) =
        (dividendMeasure
          (fun r _ =>
            sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Set.Icc 0 r))
          ω) (Set.Ioc (0 : ℝ) (t : ℝ)) := by
  intro t hb
  let E : ℝ≥0 → Ω → ℝ :=
    fun r _ => sSup ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Icc 0 r)
  have hto : Monotone (fun r : ℝ => r.toNNReal) := by -- increasing time coercion
    intro s r hsr
    exact Real.toNNReal_mono hsr
  have hmD : Monotone (fun r : ℝ => barrierStrategy X x a r.toNNReal ω) :=
    (barrierStrategy_monotone_of_le X x a hxa ω).comp hto
  have hboundedE : ∀ r : ℝ≥0, BddAbove
      ((fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) '' Icc 0 r) := by
    intro r
    obtain ⟨M, hM⟩ := levyPath_bddAbove_Icc X ω (u + r)
    refine ⟨M - X.X u ω, ?_⟩
    rintro z ⟨v, hv, rfl⟩
    apply sub_le_sub_right
    apply hM
    have huv : u + v ≤ u + r := by
      calc
        u + v = v + u := add_comm u v
        _ ≤ r + u := add_le_add_left hv.2 u
        _ = u + r := add_comm r u
    exact ⟨u + v, ⟨zero_le, huv⟩, rfl⟩
  have hmE0 : Monotone (fun r : ℝ≥0 => E r ω) :=
    intervalSup_monotone_of_bddAbove
      (fun v : ℝ≥0 => X.X (u + v) ω - X.X u ω) hboundedE
  have hmE : Monotone (fun r : ℝ => E r.toNNReal ω) :=
    hmE0.comp hto
  have hrD : ∀ r : ℝ,
      Function.rightLim (fun v : ℝ => barrierStrategy X x a v.toNNReal ω) r =
        barrierStrategy X x a r.toNNReal ω := by
    intro r
    exact rightLim_comp_toNNReal_of_rightContinuous
      (fun v : ℝ≥0 => barrierStrategy X x a v ω)
      (barrierStrategy_right_continuous_of_le X x a hxa ω) r
  have hrE : ∀ r : ℝ,
      Function.rightLim (fun v : ℝ => E v.toNNReal ω) r = E r.toNNReal ω := by
    intro r
    exact rightLim_comp_toNNReal_of_rightContinuous
      (fun v : ℝ≥0 => E v ω)
      (shiftedSup_right_continuous_of_levy X ω u) r
  have hEzero : E 0 ω = 0 := by
    simp [E]
  have hinc : barrierStrategy X x a (u + t) ω -
      barrierStrategy X x a u ω = E t ω - E 0 ω := by
    rw [hEzero, sub_zero]
    exact barrierStrategy_after_firstUpcrossing_increment_eq_shiftedSup
      X x a hxa ω u t hu hb
  simpa only [E] using
    (dividendMeasure_translated_Ioc_eq_of_increment
      (barrierStrategy X x a) E ω u t hmD hmE hrD hrE hinc)
