-- Prove2me | solution 1 for CliqueMinors.opG_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:32.380979+00:00
-- url     : https://prove2.me/submissions/945959a2-665a-4508-9a85-c42d551a159f

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
omit [Fintype V]
namespace CliqueMinors
theorem _root_.solution {G : SimpleGraph V} {x b a c u v : V} :
    (opG G x b a c).Adj u v ↔ u ≠ v ∧ u ≠ x ∧ u ≠ b ∧ v ≠ x ∧ v ≠ b ∧
      (G.Adj u v ∨ (u = a ∧ v = c) ∨ (u = c ∧ v = a)) :=
  Iff.rfl
end CliqueMinors
