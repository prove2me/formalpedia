-- Prove2me | solution 1 for BrinSquier.abelian_subgroup_of_free_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-12T22:19:56.486982+00:00
-- url     : https://prove2.me/submissions/08a4a3b8-9498-43d3-83db-c5e1a25e8e66

import Definitions.Def_BrinSquier
import Mathlib

theorem solution {G : Type*} [Group G] [IsFreeGroup G]
    (H : Subgroup G) (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) : IsCyclic H := by
  classical
  -- `H` is commutative as a group in its own right
  have hHcomm : ∀ p q : H, p * q = q * p := fun p q => Subtype.ext (hH p p.2 q q.2)
  -- Nielsen–Schreier: `H` is free on some basis
  obtain ⟨ι, ⟨bs⟩⟩ := (IsFreeGroup.nonempty_basis (G := H))
  -- transport commutativity across the basis isomorphism
  have hcomm : ∀ u v : FreeGroup ι, u * v = v * u := by
    intro u v
    have h := congrArg bs.repr (hHcomm (bs.repr.symm u) (bs.repr.symm v))
    simpa using h
  -- a free group on two distinct generators is not commutative
  have hsub : Subsingleton ι := by
    constructor
    intro i j
    by_contra hij
    set φ : FreeGroup ι →* Equiv.Perm (Fin 3) :=
      FreeGroup.lift (fun k => if k = i then Equiv.swap 0 1 else Equiv.swap 1 2) with hφ
    have h1 : φ (FreeGroup.of i) = Equiv.swap 0 1 := by simp [hφ]
    have hji : j ≠ i := fun h => hij h.symm
    have h2 : φ (FreeGroup.of j) = Equiv.swap 1 2 := by simp [hφ, hji]
    have hbad := congrArg φ (hcomm (FreeGroup.of i) (FreeGroup.of j))
    rw [map_mul, map_mul, h1, h2] at hbad
    revert hbad
    decide
  have := hsub
  have hcyc : IsCyclic (FreeGroup ι) := by
    rcases isEmpty_or_nonempty ι with h | h
    · have := h; exact isCyclic_of_subsingleton
    · haveI : Unique ι := uniqueOfSubsingleton (Classical.arbitrary ι)
      infer_instance
  have := hcyc
  exact isCyclic_of_surjective (bs.repr.symm : FreeGroup ι →* H) bs.repr.symm.surjective
