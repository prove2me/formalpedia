-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_ennreal_finite_mesh_squeeze
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:29:16.587294+00:00
-- url     : https://prove2.me/submissions/27561f90-04b0-4321-9945-3a5d02f961c5

import Mathlib.Data.ENNReal.Inv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_finite_nnreal_mesh_squeeze

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Finite ENNReal grid sandwiches reduce to NNReal and uniquely determine
the original extended nonnegative mean at every real horizon. -/
theorem solution
    (c m : ℝ≥0∞) (t : ℝ≥0) (hc : c ≠ ⊤) (hm : m ≠ ⊤)
    (hmesh : ∀ d : ℕ, 0 < d → ∃ n : ℕ,
      ((n : ℝ≥0) / (d : ℝ≥0)) ≤ t ∧
      t ≤ (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) ∧
      ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * c ≤ m ∧
      m ≤ (((n + 1 : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞)) * c) :
    m = (t : ℝ≥0∞) * c := by
  let c₀ : ℝ≥0 := c.toNNReal
  let m₀ : ℝ≥0 := m.toNNReal
  have hc₀ : (c₀ : ℝ≥0∞) = c := ENNReal.coe_toNNReal hc
  have hm₀ : (m₀ : ℝ≥0∞) = m := ENNReal.coe_toNNReal hm
  have hquot (n d : ℕ) (hd : 0 < d) :
      (((n : ℝ≥0) / (d : ℝ≥0) : ℝ≥0) : ℝ≥0∞) =
        (n : ℝ≥0∞) / (d : ℝ≥0∞) := by
    have hd₀ : (d : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    simpa using (ENNReal.coe_div (r := (d : ℝ≥0))
      (p := (n : ℝ≥0)) hd₀)
  have hNN : m₀ = t * c₀ := by
    apply avram_p2_d_future_finite_nnreal_mesh_squeeze c₀ t m₀
    intro d hd
    obtain ⟨n, hlt, hgt, hlo, hhi⟩ := hmesh d hd
    refine ⟨n, hlt, hgt, ?_, ?_⟩
    · apply ENNReal.coe_le_coe.mp
      simpa only [ENNReal.coe_mul, hquot n d hd, hc₀, hm₀] using hlo
    · apply ENNReal.coe_le_coe.mp
      simpa only [ENNReal.coe_mul, hquot (n + 1) d hd, hc₀, hm₀] using hhi
  calc
    m = (m₀ : ℝ≥0∞) := hm₀.symm
    _ = ((t * c₀ : ℝ≥0) : ℝ≥0∞) := congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞)) hNN
    _ = (t : ℝ≥0∞) * c := by simpa only [ENNReal.coe_mul, hc₀]
