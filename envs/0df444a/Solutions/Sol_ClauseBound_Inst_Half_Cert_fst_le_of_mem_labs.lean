-- Prove2me | solution 1 for ClauseBound.Inst.Half.Cert.fst_le_of_mem_labs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:37:01.648074+00:00
-- url     : https://prove2.me/submissions/a8690d76-429f-45f8-a501-f8a0427fbeac

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_Half
import Definitions.Def_ClauseBound_Inst_CertHalfPart
import Definitions.Def_ClauseBound_Inst_CertHalfTab
import Definitions.Def_ClauseBound_Inst_CertHalfSmall
import Definitions.Def_ClauseBound_Inst_CertHalf

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half ClauseBound.Inst.Half.Cert
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec
variable {α : Type} [Enc α]
namespace ClauseBound.Inst.Half.Cert
theorem _root_.solution {T : PT} {tr : Bool} {h : ℕ} {s : ℤ} {p : ℕ × List ℕ} (hp : p ∈ labs T tr h s) : p.1 ≤ 2 * h := by
  obtain ⟨j, hj, hpj⟩ := List.mem_flatMap.1 hp
  have hj' : j ≤ 2 * h := Nat.le_of_lt_succ (List.mem_range.1 hj)
  split_ifs at hpj
  · obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hpj
    exact hj'
  · exact absurd hpj List.not_mem_nil
end ClauseBound.Inst.Half.Cert
