-- Prove2me | solution 1 for ErdosRubinTaylor.dIn_univ
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:46:06.027852+00:00
-- url     : https://prove2.me/submissions/4a89a951-1893-41bc-89d9-92d2a7615919


import Mathlib
import Definitions.Def_ChoosabilityLib_ERTBasic
set_option autoImplicit true


open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable [Fintype V]
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    dIn G Set.univ v = G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  unfold dIn
  congr 1
  convert rfl
  ext w; simp

