-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:40:57.479081+00:00
-- url     : https://prove2.me/submissions/98cbde97-b3d4-4993-8bad-125b5d9b9afe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Strict original physical mesh gaps shrink to zero without horizon atoms. -/
theorem solution (T : ℝ) (hT : 0 < T) :
    (∀ n : ℕ, 0 < T / ((n : ℝ) + 2) ∧
      T - T / ((n : ℝ) + 2) < T) ∧
    Tendsto (fun n : ℕ => T - T / ((n : ℝ) + 2))
      atTop (𝓝 T) := by
  constructor
  · intro n
    have hd : 0 < ((n : ℝ) + 2) := by positivity
    have hgap : 0 < T / ((n : ℝ) + 2) := div_pos hT hd
    exact ⟨hgap, sub_lt_self T hgap⟩
  · have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [(tendsto_atTop.1 hnat b)] with n hn
      linarith
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹)
        atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp hden
    have hgap : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2))
        atTop (𝓝 (0 : ℝ)) := by
      simpa [div_eq_mul_inv] using hinv.const_mul T
    simpa using (tendsto_const_nhds.sub hgap)
