-- Prove2me | solution 1 for AvramDividend.Classical.barrier_generatorIntegrand_zero_small_negative_jump_above
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:28:21.640047+00:00
-- url     : https://prove2.me/submissions/a7cfcf4a-57a4-43da-84d4-ea13ffa0a4b6

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Set Filter Topology
open AvramDividend.Classical



theorem solution
    (W : ℝ → ℝ) (a x y : ℝ)
    (ha : 0 ≤ a) (hx : a < x) (hxy : a < x + y)
    (hy1 : -1 < y) (hy0 : y < 0) :
    SpectrallyNegativeLevy.generatorIntegrand (barrierValue W a) x y = 0 := by
  set c := divE (W a) (scaleDeriv W a)
  have hloc : barrierValue W a =ᶠ[𝓝 x] (fun z => z - a + c) := by
    filter_upwards [lt_mem_nhds hx] with z hz
    have hz0 : ¬ z < 0 := by linarith
    have hza : ¬ z ≤ a := by linarith
    simp [barrierValue, hz0, hza, c]
  have hderiv : deriv (barrierValue W a) x = 1 := by
    rw [hloc.deriv_eq]
    simp
  have hxy0 : ¬ x + y < 0 := by linarith
  have hxya : ¬ x + y ≤ a := by linarith
  have hx0 : ¬ x < 0 := by linarith
  have hxa : ¬ x ≤ a := by linarith
  have hind : (Set.Ioo (-1 : ℝ) 1).indicator 1 y = 1 := by
    rw [Set.indicator_of_mem (by constructor <;> linarith)]; rfl
  unfold SpectrallyNegativeLevy.generatorIntegrand
  rw [hderiv, Set.indicator_of_mem (show y ∈ Set.Ioo (-1:ℝ) 1 from ⟨hy1, by linarith⟩)]
  simp only [barrierValue, hxy0, hxya, hx0, hxa, if_false, Pi.one_apply]
  ring

