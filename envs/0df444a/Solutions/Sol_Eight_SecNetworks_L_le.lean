-- Prove2me | solution 1 for Eight.SecNetworks.L_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:19:21.034927+00:00
-- url     : https://prove2.me/submissions/ab584981-5ea6-4a98-9d04-92d0e370a1df

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Theorems.Thm_Paper_groupedLength_def


set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset Stepped
namespace Eight.SecNetworks
theorem _root_.solution {K g U P : ℕ} (hK : 1 ≤ K) (hg : 1 ≤ g) (hP : 1 ≤ P) (hU : U ≤ g * P) : Paper.groupedLength K g U P ≤ 2 * (g * P) := by
  have hgP : 1 ≤ g * P := Nat.mul_pos hg hP
  rw [Paper.groupedLength_def]
  refine max_le (by omega) ?_
  have hK3 : 0 < K ^ 3 := Nat.pow_pos hK
  rw [Nat.div_le_iff_le_mul_add_pred hK3]
  have h1 : K ≤ K ^ 3 := Nat.le_self_pow (by norm_num) K
  have h2 : K * U ≤ K ^ 3 * (g * P) := Nat.mul_le_mul h1 hU
  have h3 : 1 * (g * P) ≤ K ^ 3 * (g * P) := Nat.mul_le_mul_right _ hK3
  have e : K ^ 3 * (2 * (g * P)) = K ^ 3 * (g * P) + K ^ 3 * (g * P) := by ring
  omega
end Eight.SecNetworks
