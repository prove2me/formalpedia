-- Prove2me | solution 1 for ClauseBound.ParityChecks.Start.boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:21:55.57659+00:00
-- url     : https://prove2.me/submissions/87cde966-b59c-4c59-bad8-b3e7e7517f6b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_ClauseBound_ParityChecks_Start
import Theorems.Thm_ClauseBound_ParityChecks_Start_Upar_fresh_le
import Theorems.Thm_ClauseBound_ParityChecks_Start_Upar_done
import Theorems.Thm_ClauseBound_ParityChecks_Start_undRow_next
import Theorems.Thm_ClauseBound_ParityChecks_Start_undCol_next

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Start
open _root_.ParityChecks Finset
namespace ClauseBound.ParityChecks.Start
theorem _root_.solution : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E),
    2 ≤ nb → IsState r j Λ ∅ → j + 1 < r → Ups V nb r (j + 1) Λ univ ≤ Ups V nb r j Λ ∅ := by
  intro X E _ _ _ V nb r j Λ hnb hst hj
  have h1 : Upar V nb r (j + 1) Λ univ ≤ Upar V nb r j Λ ∅ := by
    refine (Upar_fresh_le V nb r (j + 1) Λ hnb (hst.later _ (Nat.lt_succ_self j))).trans (le_of_eq ?_)
    rw [Upar_done, ← mul_assoc, ← pow_succ]
    congr 2
    omega
  have h2 : Uinc nb r (j + 1) Λ (univ : Finset E) = Uinc nb r j Λ ∅ := by
    unfold Uinc; rw [undRow_next]
  have h3 : Urow nb r (j + 1) Λ (univ : Finset E) = Urow nb r j Λ ∅ := by
    unfold Urow; rw [undRow_next]
  have h4 : Ucol nb r (j + 1) Λ (univ : Finset E) = Ucol nb r j Λ ∅ := by
    unfold Ucol; rw [undCol_next r j hj]
  unfold Ups
  rw [h2, h3, h4]
  linarith
end ClauseBound.ParityChecks.Start
