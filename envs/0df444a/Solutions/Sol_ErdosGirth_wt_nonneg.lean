-- Prove2me | solution 1 for ErdosGirth.wt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:29:04.145829+00:00
-- url     : https://prove2.me/submissions/ec657977-4fb2-4abe-89b7-e45c7bf5ed76

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Sym2 (Fin m))) :
    0 ≤ wt m p S :=
  mul_nonneg (prod_nonneg fun _ _ => hp0) (prod_nonneg fun _ _ => by linarith)
end ErdosGirth
