-- Prove2me | solution 1 for BalanceSpecification.word_eq_of_projection_maps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:57:40.358192+00:00
-- url     : https://prove2.me/submissions/318c3ae2-8207-4fc4-abd0-47ff88fba18e

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A B : Type*}
namespace BalanceSpecification
theorem _root_.solution {u v : Word (A × B)}
    (h1 : u.map Prod.fst = v.map Prod.fst) (h2 : u.map Prod.snd = v.map Prod.snd) :
    u = v :=
  (List.zip_of_prod h1 h2).trans (List.zip_of_prod (xs := v) rfl rfl).symm
end BalanceSpecification
