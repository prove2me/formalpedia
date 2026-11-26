-- Prove2me | solution 1 for C6BipartiteDomination.bipartite_base_of_beta_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:47:57.942936+00:00
-- url     : https://prove2.me/submissions/2b34e83e-92ec-4585-adcf-e772b0e0df51

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
import Theorems.Thm_C6BipartiteDomination_supportB_card
import Theorems.Thm_C6BipartiteDomination_bipartiteOn_subset
import Theorems.Thm_C6BipartiteDomination_mem_BPart


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} {w : V}
    (hD : IsBipartiteOn G D)
    (hwD : w ∉ D)
    (hβ : betaCharge G D w = 1) :
    IsBipartiteOn G (BPart G D ∪ {w}) := by
  classical
  have hB : IsBipartiteOn G (BPart G D) :=
    bipartiteOn_subset G (Finset.sdiff_subset) hD
  rcases hB with ⟨c, hc⟩
  have hsupp : (supportB G D w).card = 1 := by
    rw [supportB_card]
    exact hβ
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hsupp
  have hbB : b ∈ BPart G D := by
    have : b ∈ supportB G D w := by rw [hb]; simp
    exact (Finset.mem_filter.mp this).1
  have hbNeW : b ≠ w := by
    intro heq
    exact hwD (heq ▸ (mem_BPart G D b).mp hbB |>.1)
  refine ⟨fun v => if v = w then !(c b) else c v, ?_⟩
  intro u v hu hv hadj
  rcases Finset.mem_union.mp hu with huB | huW
  · rcases Finset.mem_union.mp hv with hvB | hvW
    · have huNe : u ≠ w := by
        intro heq
        exact hwD (heq ▸ (mem_BPart G D u).mp huB |>.1)
      have hvNe : v ≠ w := by
        intro heq
        exact hwD (heq ▸ (mem_BPart G D v).mp hvB |>.1)
      simpa [huNe, hvNe] using hc huB hvB hadj
    · have hvEq : v = w := Finset.mem_singleton.mp hvW
      subst v
      have huSupp : u ∈ supportB G D w := by
        apply Finset.mem_filter.mpr
        refine ⟨huB, ?_⟩
        exact hadj.symm
      have huEq : u = b := by
        rw [hb] at huSupp
        simpa using huSupp
      subst u
      simp [hbNeW]
  · have huEq : u = w := Finset.mem_singleton.mp huW
    subst u
    rcases Finset.mem_union.mp hv with hvB | hvW
    · have hvSupp : v ∈ supportB G D w := by
        apply Finset.mem_filter.mpr
        refine ⟨hvB, ?_⟩
        exact hadj
      have hvEq : v = b := by
        rw [hb] at hvSupp
        simpa using hvSupp
      subst v
      simp [hbNeW]
    · have hvEq : v = w := Finset.mem_singleton.mp hvW
      subst v
      exact (G.irrefl hadj).elim
end C6BipartiteDomination
