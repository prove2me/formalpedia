-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.foldl_range_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:27:25.589008+00:00
-- url     : https://prove2.me/submissions/7400b5ab-ba00-4ef9-805b-62c8db4f77b2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {γ : Type} (n : ℕ) (g : γ → ℕ → γ) (a : γ) : (List.range n).foldl (fun c i => g c (min i n)) a = (List.range n).foldl g a :=
  List.foldl_ext _ _ _ fun c i hi => by rw [min_eq_left (List.mem_range.1 hi).le]
end ClauseBound.ParityChecks.CertLib
