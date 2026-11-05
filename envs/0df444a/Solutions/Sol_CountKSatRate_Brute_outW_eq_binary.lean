-- Prove2me | solution 1 for CountKSatRate.Brute.outW_eq_binary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:40:53.249884+00:00
-- url     : https://prove2.me/submissions/5706eb05-e3fe-41dc-ae90-22969c7594bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSatRate_Interfaces
import Definitions.Def_CountKSat_InOut
import Batteries.Data.Nat.Lemmas
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_CountKSatRate_Brute
import Theorems.Thm_Groundwork_Decode_toWord_eq
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open CountKSatRate CountKSatRate.Brute
open Groundwork Groundwork.Prog Groundwork.Decode CountKSat PaddedDescent PaddedDescent.F
open Sat3 (CNF)
open SatK (numSat binary)
namespace CountKSatRate.Brute
theorem _root_.solution (n : ℕ) (ψ : Fml) (N : ℕ) : outW ((List.replicate n (), ψ), N) = binary n N := by
  rw [outW, List.length_replicate, toWord_eq]
  rfl
end CountKSatRate.Brute
