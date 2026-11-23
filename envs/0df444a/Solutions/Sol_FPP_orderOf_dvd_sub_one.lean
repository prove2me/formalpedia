-- Prove2me | solution 1 for FPP.orderOf_dvd_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:00:43.035403+00:00
-- url     : https://prove2.me/submissions/bbcb9345-d76c-4d11-85d2-63f07124abde

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable

set_option autoImplicit false
open Nat
open FPP
namespace FPP
theorem _root_.solution {n : ℕ} {a : ZMod n} (h : FPP n a) :
    orderOf a ∣ n - 1 :=
  orderOf_dvd_of_pow_eq_one h
end FPP
