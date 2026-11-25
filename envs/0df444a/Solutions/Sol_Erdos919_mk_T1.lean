-- Prove2me | solution 1 for Erdos919.mk_T1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:32:16.818036+00:00
-- url     : https://prove2.me/submissions/5b580780-cc85-4271-87f0-ac6a7f98dea3

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution : #T1.{u} = ℵ₁ := mk_ord_toType _
end Erdos919
