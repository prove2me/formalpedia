-- Prove2me | solution 1 for Eight.eStar_eq_zero_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:52:46.549229+00:00
-- url     : https://prove2.me/submissions/4f2064b4-c895-4f77-b6b5-77b538e1984f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Definitions.Def_Paper_SecLevel_Recursion
import Definitions.Def_Eight_SecLevel_EStar
import Theorems.Thm_Eight_eStar_le_rho_mul_of
import Theorems.Thm_Paper_eStar_nonneg


set_option autoImplicit false
section
section
open Eight
open Paper
namespace Eight
theorem _root_.solution (hP3 : ∀ {K : ℕ} {e : ℝ}, 2 ≤ K → 0 ≤ e → Achievable K e → Achievable (9 * K ^ 16) ((rho + 2 / K) * e + 2 / K)) :
    eStar = 0 := by
  have h1 := eStar_le_rho_mul_of @hP3
  have h2 := eStar_nonneg
  have h3 : rho < 1 := by unfold rho; norm_num
  nlinarith
end Eight
