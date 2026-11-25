-- Prove2me | solution 1 for DedekindSubgroups.one_lt_of_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:20.891177+00:00
-- url     : https://prove2.me/submissions/9445008a-762b-4cbb-96a3-a6cf1d54c470

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
theorem _root_.solution (hk : 0 < k) (hinv : h * h' % k = 1) : 1 < k := by
  by_contra hc
  have : k = 1 := by omega
  subst this
  rw [Nat.mod_one] at hinv
  exact absurd hinv (by norm_num)
end DedekindSubgroups
