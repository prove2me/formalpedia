-- Prove2me | solution 1 for DeletedPrimes.tendsto_kappaK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:04:16.779563+00:00
-- url     : https://prove2.me/submissions/6091aa49-438e-4723-82af-c6714c135939

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α : ℝ} (h1 : α < 1) :
    Tendsto (fun k : ℕ => kappaK k α) atTop (𝓝 (min (1 / 2) (1 - α))) := by
  by_cases hα : α ≤ 1 / 2
  · have heq : (fun k : ℕ => kappaK k α) = fun k : ℕ => (1 - α) / (2 * (1 - α) + α ^ 2 / k) := by
      funext k; simp only [kappaK, hα, ↓reduceIte]
    have hlim : min (1 / 2) (1 - α) = (1 - α) / (2 * (1 - α) + 0) := by
      rw [min_eq_left (by linarith), add_zero, eq_div_iff (by linarith)]; ring
    rw [heq, hlim]
    exact tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _))
      (by linarith)
  · have heq : (fun k : ℕ => kappaK k α) = fun k : ℕ => (1 - α) / (1 + (1 - α) ^ 2 / k) := by
      funext k; simp only [kappaK, hα, ↓reduceIte]
    push Not at hα
    have hlim : min (1 / 2) (1 - α) = (1 - α) / (1 + 0) := by
      rw [min_eq_right (by linarith), add_zero, div_one]
    rw [heq, hlim]
    exact tendsto_const_nhds.div (tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _))
      (by norm_num)
end DeletedPrimes
