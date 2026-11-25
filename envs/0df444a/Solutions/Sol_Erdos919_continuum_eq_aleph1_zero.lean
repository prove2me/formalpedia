-- Prove2me | solution 1 for Erdos919.continuum_eq_aleph1_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:36:27.388946+00:00
-- url     : https://prove2.me/submissions/23e8cf4f-e927-42a0-a7cb-babeb947ec5b

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
universe v
namespace Erdos919
theorem _root_.solution (h : (𝔠 : Cardinal.{v}) = ℵ₁) :
    (𝔠 : Cardinal.{0}) = ℵ₁ := by
  have h' : Cardinal.lift.{v} (𝔠 : Cardinal.{0}) = Cardinal.lift.{v} (ℵ₁ : Cardinal.{0}) := by
    simpa using h
  exact Cardinal.lift_inj.1 h'
end Erdos919
