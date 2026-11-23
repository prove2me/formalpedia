-- Prove2me | solution 1 for BhangaleHypergraph.Main.categorical_product
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:29:29.788183+00:00
-- url     : https://prove2.me/submissions/b944395f-e7b2-44bb-ad66-558b00ae87b6

import Definitions.Def_BhangaleHypergraph_Main_Restricted

open BhangaleHypergraph.Main

theorem solution {V : Type} (G : SimpleGraph V) (C : ℕ)
    (hG : ¬ G.Colorable C) : ¬ (ProductComplete G C).Colorable C := by
  classical
  intro hprod
  rcases hprod with ⟨κ⟩
  have hpair (v : V) :
      ∃ i j : Fin (C + 1), κ (v, i) = κ (v, j) ∧ i ≠ j := by
    have hninj : ¬ Function.Injective (fun i : Fin (C + 1) => κ (v, i)) := by
      intro hinj
      have hc := Fintype.card_le_of_injective _ hinj
      simp only [Fintype.card_fin] at hc
      omega
    exact Function.not_injective_iff.mp hninj
  choose i j hij hne using hpair
  apply hG
  refine ⟨SimpleGraph.Coloring.mk (fun v => κ (v, i v)) ?_⟩
  intro v w hvw hrw
  by_cases hviw : i v ≠ i w
  · exact κ.valid ⟨hvw, hviw⟩ hrw
  · have hvjw : i v ≠ j w := by
      intro heq
      apply hne w
      have hiw : i v = i w := not_not.mp hviw
      exact hiw.symm.trans heq
    exact κ.valid (show (ProductComplete G C).Adj (v, i v) (w, j w) from
      ⟨hvw, hvjw⟩) (hrw.trans (hij w))
