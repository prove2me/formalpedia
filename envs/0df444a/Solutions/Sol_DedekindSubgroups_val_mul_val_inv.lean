-- Prove2me | solution 1 for DedekindSubgroups.val_mul_val_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:07:05.973131+00:00
-- url     : https://prove2.me/submissions/3ecdc1ca-2b47-4746-a103-d41a70e6c0cd

module
public import Definitions.Def_DedekindSubgroups_Parity
public import Definitions.Def_DedekindSubgroups_Main

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {k : ℕ} [NeZero k]
omit [NeZero k]
namespace DedekindSubgroups
theorem _root_.solution (hk : 1 < k) (u : (ZMod k)ˣ) :
    (u : ZMod k).val * ((u⁻¹ : (ZMod k)ˣ) : ZMod k).val % k = 1 := by
  have : Fact (1 < k) := ⟨hk⟩
  rw [← ZMod.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, ZMod.val_one]
end DedekindSubgroups
