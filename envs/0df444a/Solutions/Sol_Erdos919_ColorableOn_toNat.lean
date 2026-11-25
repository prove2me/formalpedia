-- Prove2me | solution 1 for Erdos919.ColorableOn.toNat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:35:01.85142+00:00
-- url     : https://prove2.me/submissions/36edd99e-8fbe-42d0-b398-98d9c3e41000

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_ColorableOn_of_injective

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
namespace ColorableOn
theorem _root_.solution {V : Type*} {G : SimpleGraph V} {X : Set V} {β : Type*}
    [Encodable β] (h : ColorableOn G X β) : ColorableOn G X ℕ :=
  h.of_injective _ Encodable.encode_injective
end ColorableOn
end Erdos919
