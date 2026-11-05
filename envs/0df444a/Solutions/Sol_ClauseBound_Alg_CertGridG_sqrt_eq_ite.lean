-- Prove2me | solution 1 for ClauseBound.Alg.CertGridG.sqrt_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:10:20.483451+00:00
-- url     : https://prove2.me/submissions/b48086d6-70b8-4846-9cf1-723b3eee8f96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.Alg.CertGridG
theorem _root_.solution (m : ℕ) :
    Nat.sqrt m = if (2 * Nat.sqrt (m / 4) + 1) * (2 * Nat.sqrt (m / 4) + 1) ≤ m then 2 * Nat.sqrt (m / 4) + 1 else 2 * Nat.sqrt (m / 4) := by
  have h1 := Nat.sqrt_le (m / 4)
  have h2 := Nat.lt_succ_sqrt (m / 4)
  generalize Nat.sqrt (m / 4) = t at *
  have e1 : (t + 1) * (t + 1) = t * t + 2 * t + 1 := by ring
  have e2 : (2 * t + 1 + 1) * (2 * t + 1 + 1) = 4 * (t * t) + 8 * t + 4 := by ring
  have e3 : 2 * t * (2 * t) = 4 * (t * t) := by ring
  rw [Nat.succ_eq_add_one, e1] at h2
  split_ifs with h
  · exact (Nat.eq_sqrt.2 ⟨h, by omega⟩).symm
  · exact (Nat.eq_sqrt.2 ⟨by omega, by omega⟩).symm
end ClauseBound.Alg.CertGridG
