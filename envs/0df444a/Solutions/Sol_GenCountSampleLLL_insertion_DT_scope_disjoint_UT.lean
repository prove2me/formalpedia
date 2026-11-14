-- Prove2me | solution 1 for GenCountSampleLLL.insertion_DT_scope_disjoint_UT
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:06:00.869167+00:00
-- url     : https://prove2.me/submissions/e9be11ac-3e71-4521-9789-15c141831cf2

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal
open GenCountSampleLLL

theorem solution (I : Inst) (D T : Finset (Fin I.m))
    (b : Fin I.m) (hb : b ∈ I.DT D T) : Disjoint (I.vbl b) (I.UT D T) := by
  apply Finset.disjoint_left.mpr
  intro v hvb hvU
  have hbd : b ∈ D := (Finset.mem_sdiff.mp hb).1
  have hnot : b ∉ I.N2Dc D T := (Finset.mem_sdiff.mp hb).2
  obtain ⟨c, hcN, hvc⟩ := Finset.mem_biUnion.mp hvU
  have hc : c ∈ T ∨ (c ∈ D ∧ ∃ t ∈ T, I.G.Adj t c) := by
    simpa [Inst.NDc] using hcN
  have hdist (t : Fin I.m) (ht : t ∈ T) (hadj : I.adj2D D t b) : False := by
    apply hnot
    unfold Inst.N2Dc
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hbd, ⟨t,ht,hadj⟩⟩)
  rcases hc with hcT | ⟨hcD,t,ht,htc⟩
  · by_cases hbc : b = c
    · subst b
      exact hnot (Finset.mem_union_left _ hcT)
    · have hadj : I.G.Adj c b := by
        change c ≠ b ∧ (I.vbl c ∩ I.vbl b).Nonempty
        exact ⟨Ne.symm hbc, ⟨v, Finset.mem_inter.mpr ⟨hvc,hvb⟩⟩⟩
      exact hdist c hcT (Or.inl hadj)
  · by_cases hbc : b = c
    · subst b
      exact hdist t ht (Or.inl htc)
    · have hcb : I.G.Adj c b := by
        change c ≠ b ∧ (I.vbl c ∩ I.vbl b).Nonempty
        exact ⟨Ne.symm hbc, ⟨v, Finset.mem_inter.mpr ⟨hvc,hvb⟩⟩⟩
      exact hdist t ht (Or.inr ⟨c,hcD,htc,hcb⟩)

