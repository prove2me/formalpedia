-- Prove2me | solution 1 for CliqueMinors.isMinor_K4_of_clique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:42:59.38801+00:00
-- url     : https://prove2.me/submissions/45d8ebc4-06cb-4d02-9fd7-cd3535df0beb

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_isMinor_of_clique

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]
omit [Fintype V]
namespace CliqueMinors
theorem _root_.solution {G : SimpleGraph V} {x a b c : V} (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hxc : G.Adj x c) (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    IsMinor (⊤ : SimpleGraph (Fin 4)) G := by
  refine isMinor_of_clique ![x, a, b, c] fun i j h => ?_
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl h |
    simp [hxa, hxb, hxc, hab, hac, hbc, hxa.symm, hxb.symm, hxc.symm, hab.symm, hac.symm, hbc.symm]
end CliqueMinors
