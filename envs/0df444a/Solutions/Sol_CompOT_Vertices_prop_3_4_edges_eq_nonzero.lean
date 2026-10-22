-- Prove2me | solution 1 for CompOT.Vertices.prop_3_4_edges_eq_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:03:17.695766+00:00
-- url     : https://prove2.me/submissions/312da75d-755a-454d-9103-7ff2049f0a12

import Mathlib
import Definitions.Def_CompOT_Vertices_Defs

set_option autoImplicit false
open CompOT.Vertices

theorem solution {n m : ℕ} (P : Matrix (Fin n) (Fin m) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) :
    Nat.card (supportGraph P).edgeSet = (nonzeroEntries P).card := by
  classical
  set f : Fin n × Fin m → Sym2 (Fin n ⊕ Fin m) := fun p => s(Sum.inl p.1, Sum.inr p.2) with hf
  have hinj : Function.Injective f := by
    intro p q h
    simp only [hf, Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext (Sum.inl_injective h1) (Sum.inr_injective h2)
    · simp at h1
  have hset : (supportGraph P).edgeSet = f '' {p : Fin n × Fin m | 0 < P p.1 p.2} := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet]
      constructor
      · intro h
        rcases a with i | j <;> rcases b with i' | j'
        · exact absurd h (by simp [supportGraph, supportRel])
        · exact ⟨(i, j'), h, rfl⟩
        · refine ⟨(i', j), h, ?_⟩
          simp [hf, Sym2.eq_swap]
        · exact absurd h (by simp [supportGraph, supportRel])
      · rintro ⟨⟨i, j⟩, hij, h⟩
        simp only [hf, Sym2.eq_iff] at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1; subst h2; exact hij
        · subst h1; subst h2
          exact (show (supportGraph P).Adj (Sum.inl i) (Sum.inr j) from hij).symm
  have hA : {p : Fin n × Fin m | 0 < P p.1 p.2} = ↑(nonzeroEntries P) := by
    ext p
    simp only [Set.mem_setOf_eq, nonzeroEntries, Finset.coe_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact h.ne'
    · intro h; exact lt_of_le_of_ne (hP _ _) (Ne.symm h)
  rw [hset, Nat.card_image_of_injective hinj _, hA, Nat.card_coe_set_eq, Set.ncard_coe_finset]
