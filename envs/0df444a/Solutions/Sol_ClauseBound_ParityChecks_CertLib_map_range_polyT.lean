-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.map_range_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:27:06.272099+00:00
-- url     : https://prove2.me/submissions/6845f98b-9815-42ff-b95a-9b2e629457cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {β : Type} [Enc β] {n : α → ℕ} {f : α → ℕ → β} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => (List.range (n x)).map (f x) :=
  (PolyT.map (f := fun x k => f x (min k (n x))) hf (PolyT.range hn)).congr fun x =>
    List.map_congr_left fun k hk => by rw [min_eq_left (List.mem_range.1 hk).le]
end ClauseBound.ParityChecks.CertLib
