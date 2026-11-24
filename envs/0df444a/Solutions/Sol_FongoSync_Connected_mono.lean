-- Prove2me | solution 1 for FongoSync.Connected.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:59:14.694014+00:00
-- url     : https://prove2.me/submissions/5d570b5d-5ee1-4d4e-8feb-6872037d77be

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Connected
theorem _root_.solution {E₁ E₂ : List Edge} (sub : ∀ e ∈ E₁, e ∈ E₂) {a b : Gid}
    (h : Connected E₁ a b) : Connected E₂ a b := by
  induction h with
  | refl a => exact .refl a
  | edge he => exact .edge (sub _ he)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
end Connected
end FongoSync
