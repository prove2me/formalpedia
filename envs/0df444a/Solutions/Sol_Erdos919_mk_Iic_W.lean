-- Prove2me | solution 1 for Erdos919.mk_Iic_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:34:31.60414+00:00
-- url     : https://prove2.me/submissions/fc8ff91e-2112-4277-be4c-6a34ad4d7883

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_mk_Iio_W

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution (x : W.{u}) : #(Iic x) ≤ ℵ₁ := by
  rw [← Iio_insert]
  exact mk_insert_le.trans
    ((add_le_add (mk_Iio_W x) le_rfl).trans (add_one_eq (aleph0_le_aleph 1)).le)
end Erdos919
