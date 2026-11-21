-- Prove2me | solution 1 for Eidos.Ergo.Long.sub_eq_ok_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:36:38.582256+00:00
-- url     : https://prove2.me/submissions/9b28446e-b5a4-47b0-99a2-88604fdb0397

import Std
import Definitions.Def_Eidos_Ergo_Long
import Theorems.Thm_Eidos_Ergo_Long_ofInt_eq_ok_iff
attribute [local simp] Eidos.Ergo.Long.ofInt_eq_ok_iff

set_option autoImplicit false
open Eidos Eidos.Ergo
open Eidos.Ergo.Long
namespace Eidos.Ergo.Long
theorem _root_.solution (x y z : Long) :
    sub x y = .ok z ↔ x.val - y.val = z.val := by
  exact ofInt_eq_ok_iff _ _
end Eidos.Ergo.Long
