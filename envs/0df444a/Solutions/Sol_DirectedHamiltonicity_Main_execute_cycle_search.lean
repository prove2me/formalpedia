-- Prove2me | solution 1 for DirectedHamiltonicity.Main.execute_cycle_search
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-27T03:41:57.463045+00:00
-- url     : https://prove2.me/submissions/91eff9f3-0f23-4e99-8672-5432558f34f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DirectedHamiltonicity_Main_compile_cycle_search_controller
import Theorems.Thm_DirectedHamiltonicity_Main_bounded_adaptive_cycle_controller

open TargetedSamplers DirectedHamiltonicity.Main DirectedHamiltonicity.Main.CycleReduction

theorem solution (Q : Program) (A k : ℕ) : QueryTime Q A k → ExecutesSearch Q A k := by
  intro runs
  exact compile_cycle_search_controller Q A k (bounded_adaptive_cycle_controller Q A k runs)