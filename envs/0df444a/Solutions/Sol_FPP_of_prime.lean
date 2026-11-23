-- Prove2me | solution 1 for FPP.of_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:00:52.348797+00:00
-- url     : https://prove2.me/submissions/d5c88f53-cb28-4afa-aa09-f003a8a9ffbc

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable

set_option autoImplicit false
open Nat
open FPP
namespace FPP
theorem _root_.solution {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    FPP p a :=
  ZMod.pow_card_sub_one_eq_one ha
end FPP
