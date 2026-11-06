-- Prove2me | solution 2 for Eight.SecNetworks.groupingFacts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:49:20.320959+00:00
-- url     : https://prove2.me/submissions/b7032fa5-c2b3-4ddf-9d1e-aae04fd95528

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Eight_SecNetworks_Grouping
import Theorems.Thm_Eight_SecNetworks_cheb_Y
import Theorems.Thm_Eight_SecNetworks_some_pair
import Theorems.Thm_Eight_SecNetworks_cheb_size
import Theorems.Thm_Eight_SecNetworks_some_group
import Theorems.Thm_Eight_SecNetworks_exists_good_of
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork.Colouring
variable {g K : ℕ}
namespace Eight.SecNetworks
theorem _root_.solution : GroupingFacts := by
  have pairs : ∀ (K P : ℕ) (c : Fin (3 * K ^ 8) → Fin (3 * K ^ 8) → ℕ), 2 ≤ K → (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) →
      3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + 3 * K ^ 8 * P < K ^ 3 * Y c χ γ γ'} < 2 * K ^ (3 * K ^ 8) := by
    intro K P c hK hs hP
    have h := some_pair (K := K) (by omega) hs hP
    have h8 : 0 < K ^ 8 := pow_pos (by omega) 8
    refine Nat.lt_of_mul_lt_mul_left (a := K ^ 8) ?_
    calc _ = 3 * K ^ 8 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + 3 * K ^ 8 * P < K ^ 3 * Y c χ γ γ'} := by ring
      _ < 2 * K ^ 8 * K ^ (3 * K ^ 8) := h
      _ = _ := by ring
  have groups : ∀ K : ℕ, 2 ≤ K → 3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}} < K ^ (3 * K ^ 8) := by
    intro K hK
    have h := some_group (g := 3 * K ^ 8) (K := K)
    have h2 : 0 < K ^ 2 := pow_pos (by omega) 2
    have hN : 0 < K ^ (3 * K ^ 8) := pow_pos (by omega) _
    have h6 : 1 < K ^ 6 := Nat.one_lt_pow (by omega) (by omega)
    -- K²/g = 1/(3K⁶) < 1/3
    have h' : K ^ 6 * (3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}}) ≤ K ^ (3 * K ^ 8) := by
      refine Nat.le_of_mul_le_mul_left ?_ h2
      calc _ = 3 * K ^ 8 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}} := by ring
        _ ≤ _ := h
    rcases Nat.eq_zero_or_pos (3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}}) with h0 | hp
    · rw [h0]; exact hN
    · exact lt_of_lt_of_le (by nlinarith) h'
  refine ⟨?_, pairs, fun K _ γ => cheb_size γ, groups, fun K P c hK hs hP => exists_good_of (pairs K P c hK hs hP) (groups K hK)⟩
  intro K P c hK hs hP γ γ' hne
  have h := cheb_Y hs hP hne
  have h6 : 0 < K ^ 6 := pow_pos (by omega) 6
  -- 4K⁶/g = 4/(3K²)
  refine Nat.le_of_mul_le_mul_left ?_ h6
  calc _ = 3 * K ^ 8 * #{χ : Fin (3 * K ^ 8) → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + 3 * K ^ 8 * P < K ^ 3 * Y c χ γ γ'} := by ring
    _ ≤ 4 * K ^ 6 * K ^ (3 * K ^ 8) := h
    _ = _ := by ring
end Eight.SecNetworks
