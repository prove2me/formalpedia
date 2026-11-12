-- Prove2me | solution 1 for BunkbedFalse.sub_gadget_copies_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-12T07:19:29.199335+00:00
-- url     : https://prove2.me/submissions/db4c52cd-b9fe-4f6b-8f57-e0375ec40149

import Theorems.Thm_BunkbedFalse_sub_invariants
import Theorems.Thm_BunkbedAux_gadgetE_card

open Bunkbed Bunkbed.Sub Finset

set_option maxRecDepth 100000

theorem solution :
    ∀ i j : Fin 6, i ≠ j →
      Disjoint ((gadgetE 1204).image (Sym2.map (emb i)))
        ((gadgetE 1204).image (Sym2.map (emb j))) := by
  let F : Fin 6 → Finset (Sym2 (Fin 7222)) :=
    fun i => (gadgetE 1204).image (Sym2.map (emb i))
  let D : Finset (Σ _ : Fin 6, Sym2 (Fin 7222)) := Finset.univ.sigma F
  let forget : (Σ _ : Fin 6, Sym2 (Fin 7222)) → Sym2 (Fin 7222) := fun z => z.2
  have himage : D.image forget = Finset.univ.biUnion F := by
    ext e
    simp [D, F, forget]
  have hupper : D.card ≤ 14442 := by
    calc
      D.card = ∑ i : Fin 6, (F i).card := by simp [D]
      _ ≤ ∑ _i : Fin 6, (gadgetE 1204).card := by
        exact Finset.sum_le_sum fun i _ => Finset.card_image_le
      _ = 14442 := by simp [BunkbedAux.gadgetE_card]
  have hedge_sub : (ofEdges subEdges).edgeFinset ⊆ subEdges := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet] at he
    exact he.1
  have hlower : 14442 ≤ (Finset.univ.biUnion F).card := by
    have h := Finset.card_le_card hedge_sub
    rw [BunkbedFalse.sub_invariants.1] at h
    simpa [subEdges, F] using h
  have hcard : (D.image forget).card = D.card := by
    have hi : (D.image forget).card ≤ D.card := Finset.card_image_le
    have hlo : 14442 ≤ (D.image forget).card := by
      rw [himage]
      exact hlower
    omega
  have hinj : Set.InjOn forget D := Finset.injOn_of_card_image_eq hcard
  intro i j hij
  rw [Finset.disjoint_left]
  intro e hei hej
  have zi : (⟨i, e⟩ : Σ _ : Fin 6, Sym2 (Fin 7222)) ∈ D := by
    simpa [D, F] using hei
  have zj : (⟨j, e⟩ : Σ _ : Fin 6, Sym2 (Fin 7222)) ∈ D := by
    simpa [D, F] using hej
  have zeq : (⟨i, e⟩ : Σ _ : Fin 6, Sym2 (Fin 7222)) = ⟨j, e⟩ := hinj zi zj rfl
  exact hij (congrArg Sigma.fst zeq)
