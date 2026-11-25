-- Prove2me | solution 1 for Erdos919.mk_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:13:08.450627+00:00
-- url     : https://prove2.me/submissions/d3c610f9-d2b4-4d29-9215-90b450244e04

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
theorem _root_.solution : #W.{u} = ℵ_ 2 := mk_ord_toType _
end Erdos919
