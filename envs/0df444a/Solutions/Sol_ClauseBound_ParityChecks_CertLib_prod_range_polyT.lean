-- Prove2me | solution 1 for ClauseBound.ParityChecks.CertLib.prod_range_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:27:05.169409+00:00
-- url     : https://prove2.me/submissions/e72709c2-80aa-4b00-ba92-c09da32f0bdd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_PaddedDescent_F_prodL_eq


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertLib
theorem _root_.solution {n : α → ℕ} {f : α → ℕ → ℤ} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => ∏ i ∈ Finset.range (n x), f x i :=
  (prodL_polyT (f := fun x j => f x (min j (n x))) hn hf).congr fun x => by
    rw [prodL_eq]
    exact Finset.prod_congr rfl fun j hj => by rw [min_eq_left (Finset.mem_range.1 hj).le]
end ClauseBound.ParityChecks.CertLib
