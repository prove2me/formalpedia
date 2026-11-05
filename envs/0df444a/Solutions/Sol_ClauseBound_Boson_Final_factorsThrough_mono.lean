-- Prove2me | solution 1 for ClauseBound.Boson.Final.factorsThrough_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:32:21.358243+00:00
-- url     : https://prove2.me/submissions/82f9d87b-9f51-4d7c-b48d-38e719682b2d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Boson_Final

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Final
namespace ClauseBound.Boson.Final
theorem _root_.solution {X X' : Type} {F : X → X' → ℤ} {c : ℕ} {b b' : ℤ} (h : Pieces.FactorsThrough F c b) (hb : b ≤ b') :
    Pieces.FactorsThrough F c b' := by
  obtain ⟨f, f', h1, h2, h3⟩ := h
  exact ⟨f, f', h1, fun z θ => (h2 z θ).trans_le hb, fun z θ => (h3 z θ).trans_le hb⟩
end ClauseBound.Boson.Final
