-- Prove2me | solution 1 for Emb.conf_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:46:34.04701+00:00
-- url     : https://prove2.me/submissions/ce3e99c9-c07c-41f7-abdf-f83ae5ac0b7b

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Configuration

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open Emb
variable {L : Type*} {E F : PES L} (ι : Emb E F)
namespace Emb
theorem _root_.solution {c : Set F.Event} (h : _root_.isConf F c) :
    _root_.isConf E {y | ι.f y ∈ c} :=
  ⟨fun h₁ h₂ hcf => h.1 h₁ h₂ (ι.conf hcf), fun hy hle => h.2 hy (ι.mono hle)⟩
end Emb
