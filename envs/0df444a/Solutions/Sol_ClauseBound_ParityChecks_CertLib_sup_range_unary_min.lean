-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.sup_range_unary_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:12:36.710315+00:00
-- url     : https://prove2.me/submissions/bc6d3daa-dfde-4d67-a630-13c3477f26c6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_unary_congr
import Theorems.Thm_ClauseBound_Alg_CertGridG_sup_range_unary
import Theorems.Thm_ClauseBound_Alg_CertGridG_unary_congr


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {n : α → ℕ} {f : α → ℕ → ℕ} (hn : Unary n) (hf : Unary fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    Unary fun x => (Finset.range (n x)).sup (f x) :=
  unary_congr (ClauseBound.Alg.CertGridG.sup_range_unary (f := fun x i => f x (min i (n x))) hn hf) fun x =>
    Finset.sup_congr rfl fun i hi => by rw [min_eq_left (Finset.mem_range.1 hi).le]
end ClauseBound.ParityChecks.CertLib
