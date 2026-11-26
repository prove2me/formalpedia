-- Prove2me | solution 1 for ErdosRubinTaylor.ncard_eq_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:45:43.463268+00:00
-- url     : https://prove2.me/submissions/e2d29705-e816-4cd5-8459-a154d911600a


import Definitions.Def_ChoosabilityLib_ERTBasic
import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true


open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V]
omit [Fintype V]
theorem _root_.solution [Finite V] {T : Set V} {n : ℕ} (e : G.induce T ≃g cycleGraph n) :
    T.ncard = n := by
  rw [← Nat.card_coe_set_eq, Nat.card_congr e.toEquiv, Nat.card_fin]

