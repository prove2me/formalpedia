-- Prove2me | solution 1 for C6BipartiteDomination.empty_privateExternalNeighbors_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:43:52.353198+00:00
-- url     : https://prove2.me/submissions/8ccb524e-dede-4395-b6dd-fd2445bf6368

import Definitions.Def_C6BipartiteDomination_A3
import Definitions.Def_C6BipartiteDomination_A4
import Theorems.Thm_C6BipartiteDomination_mem_privateExternalNeighbors
import Theorems.Thm_C6BipartiteDomination_bipartiteOn_subset

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} {b : V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hb : NonisolatedIn G D b)
    (hP : privateExternalNeighbors G D b = ∅) : False := by
  classical
  let E := D.erase b
  have hED : E ⊆ D := Finset.erase_subset b D
  have hEd : Dominates G E := by
    intro v hvE
    by_cases hvD : v ∈ D
    · have hvb : v = b := by
        by_contra hne
        exact hvE (Finset.mem_erase.mpr ⟨hne, hvD⟩)
      subst v
      obtain ⟨u, hu, hAdj⟩ := hb.2
      have hub : u ≠ b := by
        intro heq
        subst u
        exact G.irrefl hAdj
      exact ⟨u, Finset.mem_erase.mpr ⟨hub, hu⟩, hAdj.symm⟩
    · obtain ⟨d, hd, hAdj⟩ := hCan.1.1 hvD
      by_cases hret : ∃ u ∈ E, G.Adj u v
      · exact hret
      · have hdb : d = b := by
          by_contra hne
          exact hret ⟨d, Finset.mem_erase.mpr ⟨hne, hd⟩, hAdj⟩
        subst d
        have hvP : v ∈ privateExternalNeighbors G D b := by
          rw [mem_privateExternalNeighbors]
          refine ⟨hvD, ?_⟩
          intro u hu
          constructor
          · intro huv
            by_cases hub : u = b
            · exact hub
            · exact False.elim (hret ⟨u, Finset.mem_erase.mpr ⟨hub, hu⟩, huv⟩)
          · intro hub
            rw [hub]
            exact hAdj
        rw [hP] at hvP
        simp at hvP
  have hEbip : IsBipartiteOn G E := bipartiteOn_subset G hED hCan.1.2
  have hEbd : IsBipartiteDominatingSet G E := ⟨hEd, hEbip⟩
  have hmin := hCan.2.1 E hEbd
  have hcard : E.card + 1 = D.card := Finset.card_erase_add_one hb.1
  dsimp [E] at hmin hcard
  omega
end C6BipartiteDomination
