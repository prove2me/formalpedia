-- Prove2me | solution 1 for DedekindSubgroups.sum_sig_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:13.08494+00:00
-- url     : https://prove2.me/submissions/ed66fec4-1b36-4487-9bde-bf3e47c09168

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
theorem _root_.solution {M : Type*} [AddCommMonoid M] (hk : 0 < k) (hinv : h * h' % k = 1)
    (f : ℕ → M) : ∑ r ∈ range k, f (sig h k r) = ∑ r ∈ range k, f r := by
  have back : ∀ r < k, h' * (h * r % k) % k = r := by
    intro r hr
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, mul_comm h' h, hinv,
      one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hr]
  have forth : ∀ r < k, h * (h' * r % k) % k = r := by
    intro r hr
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, hinv,
      one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hr]
  refine Finset.sum_nbij' (fun r => h * r % k) (fun r => h' * r % k) ?_ ?_ ?_ ?_ ?_
  · intro r _; exact mem_range.mpr (Nat.mod_lt _ hk)
  · intro r _; exact mem_range.mpr (Nat.mod_lt _ hk)
  · intro r hr; exact back r (by simpa using hr)
  · intro r hr; exact forth r (by simpa using hr)
  · intro r _; rfl
end DedekindSubgroups
