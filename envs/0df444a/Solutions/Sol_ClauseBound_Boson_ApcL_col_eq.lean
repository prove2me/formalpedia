-- Prove2me | solution 1 for ClauseBound.Boson.ApcL_col_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:56:37.857556+00:00
-- url     : https://prove2.me/submissions/9c6c1710-8d23-4902-a4af-d0fc6d9ef753

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Boson_HalfList
import Theorems.Thm_ClauseBound_Boson_Half_Qk_eq


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
variable {lam h : ℕ}
variable {ℓ : Pieces.Bits lam → List ℕ}
namespace ClauseBound.Boson
theorem _root_.solution (hℓ : ∀ x, Pos (ℓ x) ∧ (ℓ x).sum = h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    ApcL ℓ h s x y u v = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ Pz (2 * h - s - i),
      topK (ℓ x) h i (s - h + i) (ℓ u : Multiset ℕ) τ * botK (ℓ v) h (h - s - i) τ (ℓ y : Multiset ℕ) := by
  unfold ApcL
  rw [Half.Qk_eq, (hℓ v).2, Multiset.sum_coe, (hℓ y).2, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum, show (h : ℤ) + (h - s - i) = 2 * h - s - i by ring]
  exact sum_congr rfl fun τ _ => mul_left_comm _ _ _
end ClauseBound.Boson
