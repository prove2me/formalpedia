-- Prove2me | solution 1 for ErdosRubinTaylor.dIn_cycle
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:46:07.033679+00:00
-- url     : https://prove2.me/submissions/2d2e94a6-4897-47cc-9356-9553e2a9c988


import Definitions.Def_ChoosabilityLib_ERTBasic
import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true


open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V]
theorem _root_.solution {T : Set V} {n : ℕ} (e : G.induce T ≃g cycleGraph n) (hn : Odd n)
    (h2 : 2 ≤ T.ncard) {u : V} (hu : u ∈ T) : dIn G T u = 2 := by
  classical
  have h3 : 3 ≤ n := by
    have : T.ncard = n := by
      rw [← Nat.card_coe_set_eq, Nat.card_congr e.toEquiv, Nat.card_fin]
    rcases hn with ⟨k, hk⟩; omega
  have hd : (G.induce T).degree ⟨u, hu⟩ = 2 := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_congr (e.mapNeighborSet ⟨u, hu⟩),
      SimpleGraph.card_neighborSet_eq_degree]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    exact SimpleGraph.cycleGraph_degree_three_le
  rw [← hd, ← SimpleGraph.card_neighborFinset_eq_degree]
  unfold dIn
  refine (Finset.card_bij (fun w _ => w.1) ?_ ?_ ?_).symm
  · intro w hw
    simp at hw
    simp [hw]
  · intro a _ b _ h; exact Subtype.ext h
  · intro b hb
    simp at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

