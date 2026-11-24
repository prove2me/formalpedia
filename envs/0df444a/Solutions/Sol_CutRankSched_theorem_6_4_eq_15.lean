-- Prove2me | solution 1 for CutRankSched.theorem_6_4_eq_15
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T22:57:12.368566+00:00
-- url     : https://prove2.me/submissions/c6072a77-c4e6-41a3-8cfd-9dfe3fde1e58

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_Instance_Valid
import Definitions.Def_CutRankSched_Feasible

set_option autoImplicit false

open CutRankSched

private lemma A_symm (I : Instance) (i j : Fin I.n) : A I i j = A I j i := by
  unfold A symp
  rw [dotProduct_comm (I.p i).1, dotProduct_comm (I.p i).2, add_comm]

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem solution (I : Instance) (L : ℕ) (hI : I.Valid) (hF : Feasible I L) :
    I.n ≤ I.m * L := by
  obtain ⟨lam, hord, hres⟩ := hF
  have hne : ∀ i, (supp (I.p i)).Nonempty := by
    intro i
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply (hI i).1
    ext q
    · by_contra hq
      have : q ∈ supp (I.p i) := by
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl hq
      simp [h] at this
    · by_contra hq
      have : q ∈ supp (I.p i) := by
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr hq
      simp [h] at this
  choose v hv using hne
  have hvT : ∀ i, v i ∈ (I.T i).verts := fun i => (hI i).2.1 (hv i)
  have hinj : Function.Injective (fun i => (lam i, v i)) := by
    intro i j hij
    simp only [Prod.mk.injEq] at hij
    obtain ⟨hl, hvv⟩ := hij
    by_contra hijne
    have hov : Overlap I i j := ⟨hijne, ⟨v i, hvT i, hvv ▸ hvT j⟩⟩
    rcases zmod2_cases (A I i j) with h0 | h1
    · exact hres i j ⟨hov, h0⟩ hl
    · rcases lt_or_gt_of_ne hijne with hlt | hgt
      · exact absurd hl (ne_of_lt (hord i j hlt h1))
      · rw [A_symm] at h1
        exact absurd hl (ne_of_gt (hord j i hgt h1))
  have := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_prod] at this
  rw [mul_comm]; exact this
