-- Prove2me | solution 1 for ClauseBound.Inst.Half.Cert.partT_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:47.420383+00:00
-- url     : https://prove2.me/submissions/1f3456b1-f238-4c75-bc9d-16c8866b4567

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf
import Theorems.Thm_ClauseBound_Inst_Half_Cert_fst_le_of_mem_labs
import Theorems.Thm_Groundwork_PolyT_elim


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.Cert
theorem _root_.solution (pad : U) (tr top : Bool) (h : ℕ) (s : ℤ) (T : PT) (a b θ : List Bool) :
    partT pad tr top h s T a b θ = ((labs T tr h s)[ofWord θ]?).elim 0 fun p => bodyT pad tr top h s T a b (min p.1 (2 * h)) p.2 := by
  unfold partT
  cases e : (labs T tr h s)[ofWord θ]? with
  | none => rfl
  | some p =>
    rw [Option.elim_some, Option.elim_some, min_eq_left (fst_le_of_mem_labs (List.mem_of_getElem? e))]
    rfl
end ClauseBound.Inst.Half.Cert
