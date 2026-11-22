-- Prove2me | solution 1 for Emb.enables_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:11:48.397331+00:00
-- url     : https://prove2.me/submissions/66f25f57-c3ba-4cc9-9acd-15c7623b3961

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Theorems.Thm_Emb_conf_restrict

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open Emb
variable {L : Type*} {E F : PES L} (ι : Emb E F)
namespace Emb
theorem _root_.solution {c : Set F.Event} {x : E.Event} (hc : _root_.isConf F c)
    (h : Configuration.enables F c (ι.f x)) :
    Configuration.enables E {y | ι.f y ∈ c} x :=
  ⟨ι.conf_restrict hc, fun _ hy hcf => h.2.1 _ hy (ι.conf hcf), fun _ hy => h.2.2 (ι.smono hy)⟩
end Emb
