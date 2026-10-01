-- Prove2me | solution 1 for Erdos142.exists_ratio_tendsto_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-30T21:49:10.918984+00:00
-- url     : https://prove2.me/submissions/ca27dd1f-c491-4422-a53d-e46a9b8399ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Erdos142Basic
import Theorems.Thm_Erdos142_exists_ratio_isLittleO

open Filter
open Erdos142

theorem solution :
    ∃ k : ℕ, 3 ≤ k ∧
      Filter.Tendsto (fun n : ℕ => (r k n : ℝ) / (r (k + 1) n : ℝ))
        Filter.atTop (nhds 0) := by
  obtain ⟨k, hk, hlittle⟩ := Erdos142.exists_ratio_isLittleO
  exact ⟨k, hk, hlittle.tendsto_div_nhds_zero⟩
