-- Prove2me | solution 1 for BollobasChromatic.Main.gnpProb_compl
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:34:33.432056+00:00
-- url     : https://prove2.me/submissions/85ab8cd9-0a7a-4eb2-8e2a-dfdfcb2ec99c

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

set_option autoImplicit false

namespace BollobasChromatic.Main.GnpComplAux

open scoped Classical

theorem card_edgeFinset_compl_add (n : ℕ) (G H : SimpleGraph (Fin n)) (hH : H = Gᶜ) :
    H.edgeFinset.card + G.edgeFinset.card = n.choose 2 := by
  have h1 : H.edgeFinset = (⊤ : SimpleGraph (Fin n)).edgeFinset \ G.edgeFinset := by
    subst hH
    ext e
    induction e using Sym2.ind with
    | h a b =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_top, Finset.mem_sdiff,
        SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj, Set.mem_compl_iff, Sym2.mem_diagSet,
        Sym2.mk_isDiag_iff]
      try tauto
  have h2 : G.edgeFinset ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset :=
    SimpleGraph.edgeFinset_mono le_top
  rw [h1, Finset.card_sdiff_add_card_eq_card h2,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]

theorem gnpWeight_compl' (n : ℕ) (p : ℝ) (G H : SimpleGraph (Fin n)) (hH : H = Gᶜ) :
    gnpWeight n p H = gnpWeight n (1 - p) G := by
  unfold gnpWeight
  have h := card_edgeFinset_compl_add n G H hH
  have e1 : n.choose 2 - H.edgeFinset.card = G.edgeFinset.card := by omega
  have e2 : H.edgeFinset.card = n.choose 2 - G.edgeFinset.card := by omega
  rw [e1, e2, sub_sub_cancel, mul_comm]

theorem gnpWeight_compl (n : ℕ) (p : ℝ) (G : SimpleGraph (Fin n)) :
    gnpWeight n p Gᶜ = gnpWeight n (1 - p) G :=
  gnpWeight_compl' n p G Gᶜ rfl

end BollobasChromatic.Main.GnpComplAux

open Filter Topology Asymptotics in
open BollobasChromatic.Main in
theorem solution (n : ℕ) (p : ℝ) (P : SimpleGraph (Fin n) → Prop) :
    gnpProb n p (fun G => P Gᶜ) = gnpProb n (1 - p) P := by
  classical
  unfold gnpProb
  rw [← (Equiv.ofBijective (fun G : SimpleGraph (Fin n) => Gᶜ) compl_involutive.bijective).sum_comp]
  refine Finset.sum_congr rfl (fun G _ => ?_)
  simp only [Equiv.ofBijective_apply, compl_compl]
  split_ifs
  · rw [BollobasChromatic.Main.GnpComplAux.gnpWeight_compl]
  · rfl
