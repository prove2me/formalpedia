-- Prove2me | solution 1 for ClauseBound.Inst.Half.Fact.cap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:19:39.282115+00:00
-- url     : https://prove2.me/submissions/da9f2c90-6de7-4222-8e73-1cd665f691e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfFact
import Theorems.Thm_ClauseBound_Inst_Half_Fact_sOf_eq
import Theorems.Thm_ClauseBound_Inst_Half_Fact_abs_le_of_lt
import Theorems.Thm_ClauseBound_Inst_Half_RcolF_eq
import Theorems.Thm_ClauseBound_Inst_Half_RrowF_eq
import Theorems.Thm_ClauseBound_Inst_Half_hF_eq


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Finset
open ClauseBound.Inst.Half.Fact
namespace ClauseBound.Inst.Half.Fact
theorem _root_.solution {c₀ c lam : ℕ} (hC : Cst c₀ c lam) (tr : Bool) (h' : ℕ) {i : ℕ} (hi : i < 4 * ClauseBound.Part.hOf lam + 1) :
    (halfF c₀ c).cap tr h' lam i = Nat.clog 2 (bif tr then ClauseBound.Part.Rcol (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam)
      else ClauseBound.Part.Rrow (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam)) := by
  have hs := abs_le.1 (abs_le_of_lt hi)
  have hc := hC.caps _ (abs_le_of_lt hi)
  change min (2 * c * lam) (Nat.clog 2 (bif tr then RcolF (hF c₀ lam) (sOf (hF c₀ lam) i) else RrowF (hF c₀ lam) (sOf (hF c₀ lam) i))) = _
  rw [hF_eq hC.h_le, sOf_eq hi, RcolF_eq hs.1, RrowF_eq hs.2]
  cases tr
  · exact min_eq_right hc.1
  · exact min_eq_right hc.2.1
end ClauseBound.Inst.Half.Fact
