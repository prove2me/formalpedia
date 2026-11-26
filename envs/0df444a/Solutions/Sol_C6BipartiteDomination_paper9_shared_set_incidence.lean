-- Prove2me | solution 1 for C6BipartiteDomination.paper9_shared_set_incidence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:55:26.437123+00:00
-- url     : https://prove2.me/submissions/406045f9-1dd0-4457-a43e-d9437711e875

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_paper9_shared_compensation_profile

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D X : Finset V} {u : V}
    (hX : X ⊆ Z0Part G D) (huB : u ∈ BPart G D) :
    sharedCompensation G D X u ⊆ (SPart G D).filter (fun q => G.Adj u q) ∧
      ∀ T : Finset V, (∀ w ∈ T, 2 ≤ kCharge G D w) →
        Disjoint T (sharedCompensation G D X u) := by
  constructor
  · intro q hq
    obtain ⟨hqS, hAdj, _⟩ := paper9_shared_compensation_profile G hX huB hq
    exact Finset.mem_filter.mpr ⟨hqS, hAdj⟩
  · intro T hT
    rw [Finset.disjoint_left]
    intro q hqT hqL
    have hkq := (paper9_shared_compensation_profile G hX huB hqL).2.2
    exact Nat.not_le_of_gt (by omega) (hT q hqT)
end C6BipartiteDomination
