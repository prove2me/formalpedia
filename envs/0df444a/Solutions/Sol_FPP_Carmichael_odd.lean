-- Prove2me | solution 1 for FPP.Carmichael.odd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:09:58.536948+00:00
-- url     : https://prove2.me/submissions/af559519-e5be-4e80-835d-a295b858551f

import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Mathlib_Data_ZMod_Units
import Definitions.Def_MillerRabin_FermatProbable

set_option autoImplicit false
open Nat
open FPP
open FPP.Carmichael
variable {n : ℕ}
namespace FPP.Carmichael
theorem _root_.solution (hn : 2 < n) (hc : Carmichael n) : Odd n := by
  rw [← not_even_iff_odd]
  rintro ⟨k, rfl⟩
  have hk : Odd (k + k - 1) :=
    Nat.Even.sub_odd (succ_le_of_lt (zero_lt_of_lt hn)) (Even.add_self k) odd_one
  specialize hc (-1)
  rw [Units.coe_neg_one, FPP, hk.neg_one_pow] at hc
  exact @ZMod.neg_one_ne_one _ ⟨hn⟩ hc
end FPP.Carmichael
