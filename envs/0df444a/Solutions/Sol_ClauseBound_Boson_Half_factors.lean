-- Prove2me | solution 1 for ClauseBound.Boson.Half.factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:56:36.58757+00:00
-- url     : https://prove2.me/submissions/3da06eb5-3015-4608-b5bf-5395d0faf9ff

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_WickPlus
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_HalfSum
import Definitions.Def_ClauseBound_Rec_Number
import Definitions.Def_ClauseBound_Boson_Half
import Theorems.Thm_ClauseBound_Boson_Half_card_Pz
import Theorems.Thm_ClauseBound_Boson_Half_two_pow_lt_big
import Theorems.Thm_ClauseBound_Rec_factorsThrough_of_sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Half
namespace ClauseBound.Boson.Half
theorem _root_.solution {Z Z' : Type} {h : ℕ} (F : Z → Z' → ℤ) (t : ℕ → ℤ) (f : ℕ → Multiset ℕ → Z → ℤ) (f' : ℕ → Multiset ℕ → Z' → ℤ)
    (hF : ∀ z z', F z z' = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ Pz (t i), f i τ z * f' i τ z')
    (hf : ∀ i ∈ range (2 * h + 1), ∀ τ ∈ Pz (t i), ∀ z, |f i τ z| ≤ 2 ^ eL h)
    (hf' : ∀ i ∈ range (2 * h + 1), ∀ τ ∈ Pz (t i), ∀ z, |f' i τ z| ≤ 2 ^ eR h) :
    Pieces.FactorsThrough F (Nat.clog 2 (∑ i ∈ range (2 * h + 1), ClauseBound.Part.pz (t i))) (2 ^ big h) := by
  refine ClauseBound.Rec.factorsThrough_of_sum ((range (2 * h + 1)).sigma fun i => Pz (t i)) F (fun x z => f x.1 x.2 z) (fun x z => f' x.1 x.2 z)
    _ _ (fun z z' => ?_) ?_ (by positivity) (fun x hx z => ?_) fun x hx z => ?_
  · rw [hF, sum_sigma']
  · rw [card_sigma]
    simp_rw [card_Pz]
    exact Nat.le_pow_clog (by norm_num) _
  · exact (hf x.1 (mem_sigma.1 hx).1 x.2 (mem_sigma.1 hx).2 z).trans_lt (two_pow_lt_big (Nat.le_add_right _ _))
  · exact (hf' x.1 (mem_sigma.1 hx).1 x.2 (mem_sigma.1 hx).2 z).trans_lt (two_pow_lt_big (Nat.le_add_left _ _))
end ClauseBound.Boson.Half
