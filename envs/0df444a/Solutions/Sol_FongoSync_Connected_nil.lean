-- Prove2me | solution 1 for FongoSync.Connected.nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:58:32.833827+00:00
-- url     : https://prove2.me/submissions/19bbed88-0170-4897-9234-536a337228e2

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias

set_option autoImplicit false
open FongoSync
namespace FongoSync
namespace Connected
theorem _root_.solution {a b : Gid} (h : Connected [] a b) : a = b := by
  induction h with
  | refl => rfl
  | edge he => cases he
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
end Connected
end FongoSync
