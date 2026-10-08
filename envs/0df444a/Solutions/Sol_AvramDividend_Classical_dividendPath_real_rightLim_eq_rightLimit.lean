-- Prove2me | solution 1 for AvramDividend.Classical.dividendPath_real_rightLim_eq_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:28:23.631199+00:00
-- url     : https://prove2.me/submissions/ff199116-d169-4e34-9705-c79e71091a74

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hmono : Monotone (fun s : ℝ≥0 => D s ω)) (t : ℝ≥0) :
    Function.rightLim (fun s : ℝ => D s.toNNReal ω) (t : ℝ) =
      rightLimit D t ω := by
  have hreal : Monotone (fun s : ℝ => D s.toNNReal ω) :=
    fun _ _ h => hmono (Real.toNNReal_mono h)
  have himage :
      (fun s : ℝ => D s.toNNReal ω) '' Ioi (t : ℝ) =
        Set.range (fun s : Ioi (t : ℝ) => D s.1.toNNReal ω) := by
    ext v
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
    · rintro ⟨⟨s, hs⟩, rfl⟩
      exact ⟨s, hs, rfl⟩
  have hrange :
      Set.range (fun s : Ioi (t : ℝ) => D s.1.toNNReal ω) =
        Set.range (fun u : Ioi t => D u.1 ω) := by
    ext v
    constructor
    · rintro ⟨⟨s, hs⟩, rfl⟩
      have hs0 : (0 : ℝ) ≤ s := (NNReal.coe_nonneg t).trans hs.le
      have hst : t < s.toNNReal := by
        apply NNReal.coe_lt_coe.mp
        change (t : ℝ) < s at hs
        simpa only [Real.coe_toNNReal s hs0] using hs
      exact ⟨⟨s.toNNReal, hst⟩, rfl⟩
    · rintro ⟨⟨u, hu⟩, rfl⟩
      refine ⟨⟨(u : ℝ), ?_⟩, ?_⟩
      · change t < u at hu
        exact_mod_cast hu
      · simp
  rw [hreal.rightLim_eq_sInf, himage, hrange, sInf_range]
  rfl
