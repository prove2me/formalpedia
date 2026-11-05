-- Prove2me | solution 1 for Eight.eStar_le_rho_mul_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:33:35.931855+00:00
-- url     : https://prove2.me/submissions/ebc3b71c-8972-4621-a4dc-d6e1365b0697

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Definitions.Def_Paper_SecLevel_Recursion
import Definitions.Def_Eight_SecLevel_EStar
import Theorems.Thm_Eight_eStar_le_of

set_option autoImplicit false
section
section
open Eight
open Paper
namespace Eight
theorem _root_.solution (hP3 : ∀ {K : ℕ} {e : ℝ}, 2 ≤ K → 0 ≤ e → Achievable K e → Achievable (9 * K ^ 16) ((rho + 2 / K) * e + 2 / K)) :
    eStar ≤ rho * eStar := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  have h1 : eStar ≤ rho * (eStar + η / 2) + η / 2 := eStar_le_of @hP3 (e := eStar + η / 2) (by linarith) (by linarith)
  have h2 : rho * (η / 2) ≤ 1 * (η / 2) := mul_le_mul_of_nonneg_right (by unfold rho; norm_num) (by linarith)
  linarith
end Eight
