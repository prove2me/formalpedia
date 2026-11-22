-- Prove2me | solution 1 for Emb.finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:41.990242+00:00
-- url     : https://prove2.me/submissions/3b98bca2-2a5b-4afc-a841-ddff6a490b0b

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
theorem _root_.solution {c : Set F.Event} (h : c.Finite) : {y | ι.f y ∈ c}.Finite :=
  h.preimage ι.inj.injOn
end Emb
