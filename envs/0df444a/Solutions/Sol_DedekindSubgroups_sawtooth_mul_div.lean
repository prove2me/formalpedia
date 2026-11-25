-- Prove2me | solution 1 for DedekindSubgroups.sawtooth_mul_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:06:30.510271+00:00
-- url     : https://prove2.me/submissions/64f7d793-2e9a-4fe1-bf7f-b72f4dd419bf

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer
public import Theorems.Thm_DedekindSubgroups_one_lt_of_inv
public import Theorems.Thm_DedekindSubgroups_sig_ne_zero
public import Theorems.Thm_DedekindSubgroups_sawtooth_div_of_lt

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution (hinv : h * h' % k = 1) {r : ℕ} (hr0 : 0 < r) (hrk : r < k) :
    sawtooth ((h * r : ℚ) / k) = (sig h k r : ℚ) / k - 1 / 2 := by
  have hk1 := one_lt_of_inv (lt_trans hr0 hrk) hinv
  have hk : (0 : ℚ) < k := by exact_mod_cast (lt_trans Nat.zero_lt_one hk1)
  have hsplit : (h * r : ℚ) / k = ((h * r / k : ℕ) : ℚ) + (sig h k r : ℚ) / k := by
    have e := Nat.div_add_mod (h * r) k
    have e' : ((h * r : ℕ) : ℚ) = (k : ℚ) * ((h * r / k : ℕ) : ℚ) + ((h * r % k : ℕ) : ℚ) := by
      exact_mod_cast e.symm
    unfold sig
    field_simp
    push_cast at e' ⊢
    linarith
  have hlt : sig h k r < k := Nat.mod_lt _ (lt_trans Nat.zero_lt_one hk1)
  have hpos : 0 < sig h k r := Nat.pos_of_ne_zero (sig_ne_zero hinv hr0 hrk)
  have hs := sawtooth_div_of_lt hpos hlt
  unfold sawtooth at hs ⊢
  rw [hsplit, Int.fract_natCast_add]
  exact hs
end DedekindSubgroups
