-- Prove2me | solution 1 for DedekindSubgroups.sig_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:43.703123+00:00
-- url     : https://prove2.me/submissions/9db2fc84-9b7f-4e5d-817b-4256d1125cdf

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution (hinv : h * h' % k = 1) {r : ℕ} (hr0 : 0 < r) (hrk : r < k) :
    sig h k r ≠ 0 := by
  intro hz
  have : h' * (h * r % k) % k = r := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, mul_comm h' h, hinv,
      one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hrk]
  unfold sig at hz
  rw [hz, mul_zero, Nat.zero_mod] at this
  omega
end DedekindSubgroups
