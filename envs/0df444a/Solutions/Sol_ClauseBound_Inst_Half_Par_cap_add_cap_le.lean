-- Prove2me | solution 1 for ClauseBound.Inst.Half.Par.cap_add_cap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:25:20.733838+00:00
-- url     : https://prove2.me/submissions/a7fcfed2-d86a-47be-98cb-2e012dfad644

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Inst_HalfPar
import Theorems.Thm_ClauseBound_Inst_Half_Par_abs_sOf_le
import Theorems.Thm_ClauseBound_Inst_Half_RcolF_eq
import Theorems.Thm_ClauseBound_Inst_Half_RrowF_eq
import Theorems.Thm_ClauseBound_Inst_Half_hF_eq


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Part ClauseBound.Inst.Rec
open ClauseBound.Inst.Half.Par
namespace ClauseBound.Inst.Half.Par
theorem _root_.solution {c₀ lam : ℕ} (c h' i : ℕ) (hh : hOf lam ≤ c₀ * lam ^ 2) :
    (halfF c₀ c).cap false h' lam i + (halfF c₀ c).cap true h' lam i ≤
      Nat.clog 2 (Rrow (hOf lam) (sOf (hOf lam) i)) + Nat.clog 2 (Rcol (hOf lam) (sOf (hOf lam) i)) := by
  have hs := abs_le.1 (abs_sOf_le (hOf lam) i)
  have h1 : (halfF c₀ c).cap false h' lam i ≤ Nat.clog 2 (Rrow (hOf lam) (sOf (hOf lam) i)) := by
    change min (2 * c * lam) (Nat.clog 2 (RrowF (hF c₀ lam) (sOf (hF c₀ lam) i))) ≤ _
    rw [hF_eq hh, RrowF_eq hs.2]
    exact min_le_right _ _
  have h2 : (halfF c₀ c).cap true h' lam i ≤ Nat.clog 2 (Rcol (hOf lam) (sOf (hOf lam) i)) := by
    change min (2 * c * lam) (Nat.clog 2 (RcolF (hF c₀ lam) (sOf (hF c₀ lam) i))) ≤ _
    rw [hF_eq hh, RcolF_eq hs.1]
    exact min_le_right _ _
  exact Nat.add_le_add h1 h2
end ClauseBound.Inst.Half.Par
