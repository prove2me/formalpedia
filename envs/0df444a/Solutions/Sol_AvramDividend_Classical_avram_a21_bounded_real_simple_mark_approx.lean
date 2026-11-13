-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_bounded_real_simple_mark_approx
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:38:45.462301+00:00
-- url     : https://prove2.me/submissions/031bc2a8-1220-4125-b6f6-0490b221a4aa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_original_Borel_mark_simple_quantization
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped Topology
noncomputable section

theorem solution :
    ∃ (f : ℕ → SimpleFunc ℝ ℝ),
      (∀ k z, |f k z| ≤ 1) ∧
      (∀ z ∈ Icc (-1 : ℝ) 0,
        Tendsto (fun k => f k z) atTop (𝓝 z)) := by
  classical
  have hBound : ∀ z ∈ Icc (-1 : ℝ) 0,
      ‖(fun x : ℝ => x) z‖ ≤ 1 := by
    intro z hz
    rcases hz with ⟨hlo, hhi⟩
    simpa [Real.norm_eq_abs] using
      (abs_le.mpr ⟨by linarith, by linarith⟩ : |z| ≤ 1)
  obtain ⟨f, hf, hlim⟩ :=
    avram_a20_bounded_original_Borel_mark_simple_quantization
      (fun z : ℝ => z) (Icc (-1 : ℝ) 0)
      measurable_id measurableSet_Icc hBound
  refine ⟨f, ?_, ?_⟩
  · intro k z
    simpa only [Real.norm_eq_abs] using hf k z
  · intro z hz
    exact hlim z hz
