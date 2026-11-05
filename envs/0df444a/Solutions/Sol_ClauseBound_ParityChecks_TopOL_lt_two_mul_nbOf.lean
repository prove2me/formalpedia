-- Prove2me | solution 1 for ClauseBound.ParityChecks.TopOL.lt_two_mul_nbOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:23:32.039539+00:00
-- url     : https://prove2.me/submissions/53fae5af-9f0e-4ccf-9440-87974d20fb14

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_PaddedDescent_Choice
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_CountKSat_Top_Count
import Definitions.Def_ClauseBound_ParityChecks_TopOL
import Theorems.Thm_ClauseBound_ParityChecks_TopOL_LD_pos
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.TopOL
open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (theta bsum leafC)
open PaddedDescent.F.Mark (WfL occ nSat)
namespace ClauseBound.ParityChecks.TopOL
theorem _root_.solution {n Δ : ℕ} (hΔ : 1 ≤ Δ) (h : 1 ≤ nbOf n Δ) : n < 2 * (nbOf n Δ * LD Δ) := by
  have h1 := Nat.lt_mul_div_succ n (LD_pos hΔ)
  have h2 : LD Δ * (n / LD Δ + 1) = nbOf n Δ * LD Δ + LD Δ := by rw [nbOf]; ring
  have h3 : LD Δ ≤ nbOf n Δ * LD Δ := Nat.le_mul_of_pos_left _ h
  omega
end ClauseBound.ParityChecks.TopOL
