-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.hyp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:52:00.142405+00:00
-- url     : https://prove2.me/submissions/428af48d-3985-4752-97eb-05fe06a273b5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_start_parOf
import Theorems.Thm_ClauseBound_ParityChecks_small_parOf
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_two_le_nb
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_series
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_drift

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
open ClauseBound.ParityChecks.Params.Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b
namespace ClauseBound.ParityChecks.Params.Big
theorem _root_.solution : Hyp (parOf n Δ m) (2 ^ n) (2 / 2 ^ (10 * n)) where
  nb_two := b.two_le_nb
  r_pos := by
    show 1 ≤ rOf n (beta0 m (nbOf n Δ))
    unfold rOf; omega
  m_pos := by
    show 1 ≤ m
    have := b.hnb; omega
  β_pos := by
    show 2 ≤ n + beta0 m (nbOf n Δ) + beta1 m (i0Of n) + 2
    omega
  start := start_parOf n Δ m
  series := b.series
  drift := b.drift
  small := small_parOf n Δ m
end ClauseBound.ParityChecks.Params.Big
