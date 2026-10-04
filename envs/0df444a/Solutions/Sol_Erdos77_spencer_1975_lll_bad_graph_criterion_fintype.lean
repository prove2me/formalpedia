-- Prove2me | solution 1 for Erdos77.spencer_1975_lll_bad_graph_criterion_fintype
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T13:20:20.127364+00:00
-- url     : https://prove2.me/submissions/acc86d6d-443c-44ae-bf5a-3a801e4ceef3

import Theorems.Thm_Erdos77_spencer_1975_lll_bad_graph_criterion_fin_core

theorem solution (V : Type*) [Fintype V] [DecidableEq V]
    (k : Nat) (hk : 2 <= k) (hkn : k <= Fintype.card V)
    (hcond :
      (4 : Real) * (Nat.choose k 2 : Real) *
          (Nat.choose (Fintype.card V - 2) (k - 2) : Real) *
          (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) :
    Exists fun G : SimpleGraph V =>
      And (Not (Exists fun s : Finset V => And (s.card = k) (G.IsClique s)))
        (Not (Exists fun s : Finset V => And (s.card = k) ((Compl.compl G).IsClique s))) := by
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  have hfin := Erdos77.spencer_1975_lll_bad_graph_criterion_fin_core k
    (Fintype.card V) hk hkn hcond
  rcases hfin with ⟨H, hH₁, hH₂⟩
  refine ⟨H.comap e, ?_, ?_⟩
  · intro h
    rcases h with ⟨s, hs_card, hs_clique⟩
    have hmap : (H.comap e).map e.toEmbedding = H := by
      ext a b
      constructor
      · rintro ⟨_, x, y, hxy, rfl, rfl⟩
        exact hxy
      · intro hab
        exact ⟨hab.ne, e.symm a, e.symm b, by simpa using hab,
          e.apply_symm_apply a, e.apply_symm_apply b⟩
    have hs' : H.IsClique (s.map e.toEmbedding) := by
      simpa only [hmap] using hs_clique.finsetMap (f := e.toEmbedding)
    apply hH₁
    refine ⟨s.map e.toEmbedding, ?_, hs'⟩
    simpa using hs_card
  · intro h
    rcases h with ⟨s, hs_card, hs_clique⟩
    have hmap : ((H.comap e)ᶜ).map e.toEmbedding = Hᶜ := by
      ext a b
      constructor
      · rintro ⟨_, x, y, hxy, rfl, rfl⟩
        simpa [SimpleGraph.comap] using hxy
      · intro hab
        have hab' : a ≠ b ∧ ¬ H.Adj a b := by simpa using hab
        refine ⟨hab'.1, e.symm a, e.symm b, ?_, e.apply_symm_apply a,
          e.apply_symm_apply b⟩
        simpa [SimpleGraph.comap] using hab'
    have hs' : Hᶜ.IsClique (s.map e.toEmbedding) := by
      simpa only [hmap] using hs_clique.finsetMap (f := e.toEmbedding)
    apply hH₂
    refine ⟨s.map e.toEmbedding, ?_, hs'⟩
    simpa using hs_card
