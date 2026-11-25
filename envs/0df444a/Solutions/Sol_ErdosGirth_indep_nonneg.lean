-- Prove2me | solution 1 for ErdosGirth.indep_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:15.952298+00:00
-- url     : https://prove2.me/submissions/9ac97284-2951-483a-b86f-4415f99bdddb

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution {m t : ℕ} (S : Finset (Sym2 (Fin m))) : 0 ≤ indep m t S :=
  sum_nonneg fun _ _ => by split_ifs <;> norm_num
end ErdosGirth
