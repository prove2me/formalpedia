-- Prove2me | solution 1 for ErdosGirth.cyc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:15.248853+00:00
-- url     : https://prove2.me/submissions/1efa1de4-d991-4523-b32a-43f78bb367b7

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
open Classical
namespace ErdosGirth
theorem _root_.solution {m g : ℕ} (S : Finset (Sym2 (Fin m))) (u : Fin m) : 0 ≤ cyc m g S u :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num
end ErdosGirth
