-- Prove2me | solution 1 for Erdos919.mk_Iio_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:32:49.778801+00:00
-- url     : https://prove2.me/submissions/f46bab72-a122-4e3c-8f2e-3ef3d88bfb28

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
public import Theorems.Thm_Erdos919_mk_W
public import Theorems.Thm_Erdos919_le_aleph1_of_lt_aleph2

set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section
namespace Erdos919
theorem _root_.solution (x : W.{u}) : #(Iio x) ≤ ℵ₁ :=
  le_aleph1_of_lt_aleph2 (by simpa [mk_W] using mk_Iio_lt x (by rw [mk_W, type_toType]))
end Erdos919
