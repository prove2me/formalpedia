-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.undCol_next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:11:50.324199+00:00
-- url     : https://prove2.me/submissions/b45afc59-6312-406d-8e17-248ef43b17cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution (r j : ℕ) (h : j + 1 < r) : undCol r (j + 1) (univ : Finset E) = undCol r j (∅ : Finset E) := by
  funext e
  unfold undCol
  simp only [mem_univ, if_true, notMem_empty, if_false]
  omega
end ClauseBound.ParityChecks.Start
