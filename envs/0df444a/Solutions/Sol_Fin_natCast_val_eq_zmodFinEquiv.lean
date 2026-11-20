-- Prove2me | solution 1 for Fin.natCast_val_eq_zmodFinEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:54:46.189535+00:00
-- url     : https://prove2.me/submissions/4444c084-a25b-46e8-95f8-b4a19dd91b71

module
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_ForbiddenMatrix_Mathlib_Data_ZMod_Basic

set_option autoImplicit true
@[expose] public section
public section
namespace Fin
theorem _root_.solution {n : ℕ} [NeZero n] (a : Fin n) :
    a = ZMod.finEquiv n a := by
  obtain _ | n := n
  · obtain ⟨_, ⟨⟩⟩ := a
  · change (⟨_, _⟩ : ZMod (n + 1)) = ⟨_, _⟩
    congr
    simp
    lia
end Fin
