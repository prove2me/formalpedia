-- Prove2me | solution 1 for FPP.isUnit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:00:41.569552+00:00
-- url     : https://prove2.me/submissions/fdfae099-2415-48f8-8d34-2edcc9632fb0

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable

set_option autoImplicit false
open Nat
open FPP
namespace FPP
theorem _root_.solution {n : ℕ} [hn : Fact (1 < n)] {a : ZMod n} (h : FPP n a) :
    IsUnit a :=
  IsUnit.of_pow_eq_one h (by have := hn.out; omega)
end FPP
