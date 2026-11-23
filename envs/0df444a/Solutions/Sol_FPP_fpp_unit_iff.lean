-- Prove2me | solution 1 for FPP.fpp_unit_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:00:51.583855+00:00
-- url     : https://prove2.me/submissions/e5f396da-5524-4827-87ce-96bacd272fb3

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable

set_option autoImplicit false
open Nat
open FPP
namespace FPP
theorem _root_.solution {n : ℕ} {a : (ZMod n)ˣ} :
    FPP n a ↔ a ^ (n - 1) = 1 := by
  rw [Units.ext_iff]
  push_cast
  rfl
end FPP
