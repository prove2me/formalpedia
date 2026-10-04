-- Prove2me | solution 1 for Conway99Formal.SrgCore.edge_in_12_induced_C4_distinct
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T04:02:50.001124+00:00
-- url     : https://prove2.me/submissions/da2f8a4a-6144-45cb-b900-da1d0bab5b8c

import Theorems.Thm_Conway99Formal_SrgCore_neighborhood_internal_degree
import Theorems.Thm_Conway99Formal_SrgCore_nonadjacent_common_neighbors_finset
import Mathlib

namespace Conway99Formal.SrgCore
end Conway99Formal.SrgCore

set_option autoImplicit false

/-! Graph-owned parameter and adjacency identities for a hypothetical SRG(99,14,1,2).
Sources: `Conway99/Conway99/Core.lean` §§1–3, 8.1;
`Conway99/Conway99/Claims/C01srgcorealgebra.lean` §§0, 3, 6;
`Conway99/results/R005_star_complement_square_discriminant.md`.
-/

namespace Conway99Formal.SrgCore

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



theorem degree (h : G.IsSRGWith 99 14 1 2) (v : V) : G.degree v = 14 :=
  h.regular.degree_eq v




















































end Conway99Formal.SrgCore

set_option autoImplicit false

/-! Graph-owned parameter and adjacency identities for a hypothetical SRG(99,14,1,2).
Sources: `Conway99/Conway99/Core.lean` §§1–3, 8.1;
`Conway99/Conway99/Claims/C01srgcorealgebra.lean` §§0, 3, 6;
`Conway99/results/R005_star_complement_square_discriminant.md`.
-/

open Conway99Formal.SrgCore

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Conway99Formal.SrgCore in
theorem solution (h : G.IsSRGWith 99 14 1 2)
    (x y : V) (hxy : G.Adj x y) :
    ((univ : Finset (V × V)).filter fun p =>
      G.Adj y p.1 ∧ G.Adj p.1 p.2 ∧ G.Adj p.2 x ∧
        ¬ G.Adj x p.1 ∧ ¬ G.Adj y p.2 ∧ p.1 ≠ x ∧ p.2 ≠ y).card = 12 := by
  classical
  let A : Finset V := (G.neighborFinset y \ {x}) \ G.neighborFinset x
  let F : Finset (V × V) := (univ : Finset (V × V)).filter fun p =>
    G.Adj y p.1 ∧ G.Adj p.1 p.2 ∧ G.Adj p.2 x ∧
      ¬ G.Adj x p.1 ∧ ¬ G.Adj y p.2 ∧ p.1 ≠ x ∧ p.2 ≠ y
  change F.card = 12
  have hAmem (a : V) : a ∈ A ↔ G.Adj y a ∧ a ≠ x ∧ ¬ G.Adj x a := by
    simp only [A, mem_sdiff, mem_singleton, G.mem_neighborFinset]
    tauto
  have hFmem (p : V × V) : p ∈ F ↔
      G.Adj y p.1 ∧ G.Adj p.1 p.2 ∧ G.Adj p.2 x ∧
        ¬ G.Adj x p.1 ∧ ¬ G.Adj y p.2 ∧ p.1 ≠ x ∧ p.2 ≠ y := by
    simp only [F, mem_filter, mem_univ, true_and]
  have hsecond (a : V) (ha : a ∈ A) : ∃! b : V, (a, b) ∈ F := by
    obtain ⟨hya, hax, hnxa⟩ := (hAmem a).mp ha
    have hC := nonadjacent_common_neighbors_finset G h x a hax.symm hnxa
    have hyC : y ∈ G.neighborFinset x ∩ G.neighborFinset a := by
      apply mem_inter.mpr
      constructor
      · simpa only [G.mem_neighborFinset] using hxy
      · simpa only [G.mem_neighborFinset] using hya.symm
    have hrem : ((G.neighborFinset x ∩ G.neighborFinset a).erase y).card = 1 := by
      rw [card_erase_of_mem hyC, hC]
    obtain ⟨b, hb, hub⟩ := card_eq_one_iff_existsUnique.mp hrem
    obtain ⟨hby, hbC⟩ := mem_erase.mp hb
    obtain ⟨hxb, hab⟩ := mem_inter.mp hbC
    have hxb' : G.Adj x b := by simpa only [G.mem_neighborFinset] using hxb
    have hab' : G.Adj a b := by simpa only [G.mem_neighborFinset] using hab
    have hnyb : ¬ G.Adj y b := by
      intro hyb
      have hlocal := neighborhood_internal_degree G h y b hyb
      obtain ⟨z, hz⟩ := card_eq_one.mp hlocal
      have hxlocal : x ∈ G.neighborFinset y ∩ G.neighborFinset b := by
        apply mem_inter.mpr
        constructor
        · simpa only [G.mem_neighborFinset] using hxy.symm
        · simpa only [G.mem_neighborFinset] using hxb'.symm
      have halocal : a ∈ G.neighborFinset y ∩ G.neighborFinset b := by
        apply mem_inter.mpr
        constructor
        · simpa only [G.mem_neighborFinset] using hya
        · simpa only [G.mem_neighborFinset] using hab'.symm
      have hxz : x = z := by simpa [hz] using hxlocal
      have haz : a = z := by simpa [hz] using halocal
      exact hax (haz.trans hxz.symm)
    have hbF : (a, b) ∈ F := (hFmem (a, b)).mpr
      ⟨hya, hab', hxb'.symm, hnxa, hnyb, hax, hby⟩
    refine ⟨b, hbF, ?_⟩
    intro c hc
    obtain ⟨_, hac, hcx, _, _, _, hcy⟩ := (hFmem (a, c)).mp hc
    have hcC : c ∈ (G.neighborFinset x ∩ G.neighborFinset a).erase y := by
      apply mem_erase.mpr
      constructor
      · exact hcy
      · apply mem_inter.mpr
        constructor
        · simpa only [G.mem_neighborFinset] using hcx.symm
        · simpa only [G.mem_neighborFinset] using hac
    exact hub c hcC
  have hFtoA (p : V × V) (hp : p ∈ F) : p.1 ∈ A := by
    obtain ⟨hya, _, _, hnxa, _, hax, _⟩ := (hFmem p).mp hp
    exact (hAmem p.1).mpr ⟨hya, hax, hnxa⟩
  have hFcard : F.card = A.card := by
    refine Finset.card_bij (s := F) (t := A) (fun p _ => p.1) ?_ ?_ ?_
    · exact hFtoA
    · intro p hp q hq heq
      obtain ⟨b, hb, hub⟩ := hsecond p.1 (hFtoA p hp)
      have hp' : (p.1, p.2) ∈ F := by simpa only [Prod.mk.eta] using hp
      have hq' : (p.1, q.2) ∈ F := by simpa only [heq, Prod.mk.eta] using hq
      have hp2 : p.2 = b := hub p.2 hp'
      have hq2 : q.2 = b := hub q.2 hq'
      exact Prod.ext heq (hp2.trans hq2.symm)
    · intro a ha
      obtain ⟨b, hb, _⟩ := hsecond a ha
      exact ⟨(a, b), hb, rfl⟩
  have hxy' : x ∈ G.neighborFinset y := by
    simpa only [G.mem_neighborFinset] using hxy.symm
  have hxsub : ({x} : Finset V) ⊆ G.neighborFinset y :=
    singleton_subset_iff.mpr hxy'
  have hBcard : (G.neighborFinset y \ {x}).card = 13 := by
    rw [card_sdiff_of_subset hxsub, card_singleton,
      G.card_neighborFinset_eq_degree, degree G h y]
  have hIx : x ∉ G.neighborFinset x := G.notMem_neighborFinset_self x
  have hset : ((G.neighborFinset y \ {x}) ∩ G.neighborFinset x) =
      G.neighborFinset y ∩ G.neighborFinset x := by
    ext v
    by_cases hv : v = x
    · subst v
      simp [hIx]
    · simp [hv]
  have hIcard : ((G.neighborFinset y \ {x}) ∩ G.neighborFinset x).card = 1 := by
    rw [hset]
    simpa only [inter_comm] using neighborhood_internal_degree G h x y hxy
  have hsplit := card_sdiff_add_card_inter
    (G.neighborFinset y \ {x}) (G.neighborFinset x)
  change A.card + ((G.neighborFinset y \ {x}) ∩ G.neighborFinset x).card =
    (G.neighborFinset y \ {x}).card at hsplit
  rw [hFcard]
  omega
