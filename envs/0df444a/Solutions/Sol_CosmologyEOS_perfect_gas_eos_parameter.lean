-- Prove2me | solution 1 for CosmologyEOS.perfect_gas_eos_parameter
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:09:54.208598+00:00
-- url     : https://prove2.me/submissions/623c9cb1-6125-4fa7-b589-ef25e1c61c49

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology
open CosmologyEOS

theorem solution (ρ R T c : ℝ) (hρ : ρ ≠ 0) (hc : c ≠ 0)
    (hRT : 0 ≤ R * T) :
    eosParameter (ρ * R * T) (ρ * c ^ 2) = (Real.sqrt (R * T)) ^ 2 / c ^ 2 ∧
      eosParameter (ρ * (Real.sqrt (R * T)) ^ 2) (ρ * c ^ 2) = (Real.sqrt (R * T)) ^ 2 / c ^ 2 := by
  unfold eosParameter
  rw [Real.sq_sqrt hRT]
  constructor <;> field_simp
