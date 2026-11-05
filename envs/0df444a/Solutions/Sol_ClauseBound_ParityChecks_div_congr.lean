-- Prove2me | solution 1 for ClauseBound.ParityChecks.div_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:21:16.942234+00:00
-- url     : https://prove2.me/submissions/32c97639-0054-469c-9297-1e19aabb4588

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Congr

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Congr
variable {X : Type} [Fintype X] {m : ℕ} (V : X → Finset (Fin m)) (nb r : ℕ)
namespace ClauseBound.ParityChecks
theorem _root_.solution {β r : ℕ} {a b : ℤ} (h : a ≡ 2 ^ r * b [ZMOD 2 ^ (β + r)]) : a / 2 ^ r ≡ b [ZMOD 2 ^ β] := by
  obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd.1 h)
  have ha : a = 2 ^ r * (b - 2 ^ β * t) := by
    have : a = 2 ^ r * b - 2 ^ (β + r) * t := by linarith
    rw [this, pow_add]
    ring
  have h2 : (2 : ℤ) ^ r ≠ 0 := by positivity
  rw [ha, Int.mul_ediv_cancel_left _ h2]
  refine Int.modEq_iff_dvd.2 ⟨t, ?_⟩
  ring
end ClauseBound.ParityChecks
