-- Prove2me | solution 1 for BollobasChromatic.Main.display_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:41:08.173023+00:00
-- url     : https://prove2.me/submissions/238052e5-98a9-4189-880e-83ad1668a35c

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

set_option autoImplicit false

namespace BollobasChromatic.Main.D6Aux

open BollobasChromatic.Main
open scoped Classical

/-- `s` spans an `r`-clique of `G` sharing no edge with any other `r`-clique. -/
def IsoAt {n : ℕ} (r : ℕ) (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) : Prop :=
  G.IsNClique r s ∧ ∀ t : Finset (Fin n), G.IsNClique r t → t ≠ s → (s ∩ t).card ≤ 1

lemma weight_equiv {n : ℕ} (p : ℝ) (e : Fin n ≃ Fin n) (G : SimpleGraph (Fin n)) :
    gnpWeight n p (e.simpleGraph G) = gnpWeight n p G := by
  have h : (e.simpleGraph G).edgeFinset.card = G.edgeFinset.card := by
    have iso : e.simpleGraph G ≃g G := SimpleGraph.Iso.comap e.symm G
    convert iso.card_edgeFinset_eq
  unfold gnpWeight
  rw [h]

lemma isNClique_equiv {n r : ℕ} (e : Fin n ≃ Fin n) (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) :
    (e.simpleGraph G).IsNClique r (s.map e.toEmbedding) ↔ G.IsNClique r s := by
  simp only [SimpleGraph.isNClique_iff, Finset.card_map, SimpleGraph.IsClique, Finset.coe_map,
    Equiv.coe_toEmbedding]
  rw [Set.InjOn.pairwise_image e.injective.injOn]
  have hfun : Function.onFun (e.simpleGraph G).Adj ⇑e = G.Adj := by
    funext x y
    simp [Function.onFun]
  rw [hfun]

lemma isoAt_equiv {n r : ℕ} (e : Fin n ≃ Fin n) (G : SimpleGraph (Fin n))
    (s : Finset (Fin n)) :
    IsoAt r (e.simpleGraph G) (s.map e.toEmbedding) ↔ IsoAt r G s := by
  unfold IsoAt
  rw [isNClique_equiv]
  apply and_congr Iff.rfl
  constructor
  · intro h t ht hts
    have := h (t.map e.toEmbedding) ((isNClique_equiv e G t).2 ht)
      (by intro hh; exact hts (Finset.map_injective _ hh))
    rwa [← Finset.map_inter, Finset.card_map] at this
  · intro h t ht hts
    obtain ⟨t', rfl⟩ : ∃ t', t = t'.map e.toEmbedding :=
      ⟨t.map e.symm.toEmbedding, by ext x; simp⟩
    rw [isNClique_equiv] at ht
    rw [← Finset.map_inter, Finset.card_map]
    exact h t' ht (by rintro rfl; exact hts rfl)

/-- `P(s is an isolated r-clique)`. -/
noncomputable def gIso (n : ℕ) (p : ℝ) (r : ℕ) (s : Finset (Fin n)) : ℝ :=
  ∑ G : SimpleGraph (Fin n), gnpWeight n p G * (if IsoAt r G s then (1 : ℝ) else 0)

lemma gIso_equiv (n : ℕ) (p : ℝ) (r : ℕ) (e : Fin n ≃ Fin n) (s : Finset (Fin n)) :
    gIso n p r (s.map e.toEmbedding) = gIso n p r s := by
  unfold gIso
  rw [← Equiv.sum_comp e.simpleGraph]
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [weight_equiv]
  simp only [isoAt_equiv]

lemma exists_perm_map {n : ℕ} (W s : Finset (Fin n)) (h : W.card = s.card) :
    ∃ e : Fin n ≃ Fin n, W.map e.toEmbedding = s := by
  let f : {x // x ∈ W} ≃ {x // x ∈ s} := Finset.equivOfCardEq h
  refine ⟨f.extendSubtype, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact Equiv.extendSubtype_mem f x hx
  · rw [Finset.card_map, h]

lemma isolated_eq_sum {n r : ℕ} (G : SimpleGraph (Fin n)) :
    (isolatedCliqueCount G r : ℝ) =
      ∑ s : Finset (Fin n), if IsoAt r G s then (1 : ℝ) else 0 := by
  unfold isolatedCliqueCount
  have : (G.cliqueFinset r).filter
      (fun s => ∀ t ∈ G.cliqueFinset r, t ≠ s → (s ∩ t).card ≤ 1) =
      Finset.univ.filter (IsoAt r G) := by
    ext s
    simp [IsoAt, SimpleGraph.mem_cliqueFinset_iff]
  rw [this, Finset.card_filter]
  push_cast
  rfl

lemma baseSet_card {n r : ℕ} (hrn : r ≤ n) : (baseSet n r).card = r := by
  unfold baseSet
  rw [Fin.card_filter_val_lt]
  omega

lemma sum_g (n : ℕ) (p : ℝ) (r : ℕ) (hrn : r ≤ n) :
    ∑ s : Finset (Fin n), gIso n p r s = (n.choose r : ℝ) * gIso n p r (baseSet n r) := by
  have hW := baseSet_card (n := n) hrn
  have key : ∀ s : Finset (Fin n),
      gIso n p r s = if s.card = r then gIso n p r (baseSet n r) else 0 := by
    intro s
    split_ifs with hs
    · obtain ⟨e, he⟩ := exists_perm_map (baseSet n r) s (by rw [hW, hs])
      rw [← he, gIso_equiv]
    · unfold gIso
      refine Finset.sum_eq_zero fun G _ => ?_
      rw [if_neg]
      · simp
      · intro h; exact hs h.1.card_eq
  rw [Finset.sum_congr rfl (fun s _ => key s), Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, nsmul_eq_mul]
  congr 1
  have : (Finset.univ.filter fun s : Finset (Fin n) => s.card = r) =
      Finset.powersetCard r Finset.univ := by
    ext s
    simp [Finset.mem_powersetCard]
  rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma pointwise {n r : ℕ} (hrn : r ≤ n) (G : SimpleGraph (Fin n)) :
    (if G.IsClique (baseSet n r : Set (Fin n)) then (1 : ℝ) else 0) -
      (if G.IsClique (baseSet n r : Set (Fin n)) then
        ∑ l ∈ Finset.Icc 2 (r - 1), (cliquesMeeting G r l : ℝ) else 0) ≤
      if IsoAt r G (baseSet n r) then (1 : ℝ) else 0 := by
  have hW := baseSet_card (n := n) hrn
  have hZ : 0 ≤ ∑ l ∈ Finset.Icc 2 (r - 1), (cliquesMeeting G r l : ℝ) :=
    Finset.sum_nonneg fun l _ => Nat.cast_nonneg _
  by_cases hA : G.IsClique (baseSet n r : Set (Fin n))
  · rw [if_pos hA, if_pos hA]
    by_cases hI : IsoAt r G (baseSet n r)
    · rw [if_pos hI]; linarith
    · rw [if_neg hI]
      have hN : G.IsNClique r (baseSet n r) := ⟨hA, hW⟩
      have : ∃ t : Finset (Fin n), G.IsNClique r t ∧ t ≠ baseSet n r ∧
          1 < (baseSet n r ∩ t).card := by
        unfold IsoAt at hI
        push_neg at hI
        exact hI hN
      obtain ⟨t, ht, htW, hcard⟩ := this
      set l := (t ∩ baseSet n r).card with hl
      have hl2 : 2 ≤ l := by rw [hl, Finset.inter_comm]; omega
      have hlr : l < r := by
        rw [← hW, hl]
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_right, ?_⟩
        intro heq
        apply htW
        have hsub : baseSet n r ⊆ t := by
          rw [← heq]; exact Finset.inter_subset_left
        exact (Finset.eq_of_subset_of_card_le hsub (by rw [ht.card_eq, hW])).symm
      have hmem : l ∈ Finset.Icc 2 (r - 1) := Finset.mem_Icc.2 ⟨hl2, by omega⟩
      have hpos : (1 : ℝ) ≤ (cliquesMeeting G r l : ℝ) := by
        have : 0 < cliquesMeeting G r l := by
          unfold cliquesMeeting
          apply Finset.card_pos.2
          refine ⟨t, ?_⟩
          rw [Finset.mem_filter, SimpleGraph.mem_cliqueFinset_iff]
          exact ⟨ht, rfl⟩
        exact_mod_cast this
      have := Finset.single_le_sum (f := fun l => (cliquesMeeting G r l : ℝ))
        (fun l _ => Nat.cast_nonneg _) hmem
      linarith
  · rw [if_neg hA, if_neg hA]
    split_ifs <;> norm_num

end BollobasChromatic.Main.D6Aux

open Filter Topology Asymptotics Classical BollobasChromatic.Main in
theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (n r : ℕ) (hrn : r ≤ n) :
    (n.choose r : ℝ) *
        (gnpProb n p (fun G => G.IsClique (baseSet n r : Set (Fin n))) -
          gnpExp n p (fun G => if G.IsClique (baseSet n r : Set (Fin n)) then
            ∑ l ∈ Finset.Icc 2 (r - 1), (cliquesMeeting G r l : ℝ) else 0)) ≤
      gnpExp n p (fun G => (isolatedCliqueCount G r : ℝ)) := by
  have hw : ∀ G, 0 ≤ gnpWeight n p G := fun G => by
    unfold gnpWeight
    exact mul_nonneg (pow_nonneg hp0.le _) (pow_nonneg (by linarith) _)
  have hE : gnpExp n p (fun G => (isolatedCliqueCount G r : ℝ)) =
      ∑ s : Finset (Fin n), D6Aux.gIso n p r s := by
    unfold gnpExp D6Aux.gIso
    simp_rw [D6Aux.isolated_eq_sum, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hE, D6Aux.sum_g n p r hrn]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  unfold gnpProb gnpExp D6Aux.gIso
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro G _
  have h2 := mul_le_mul_of_nonneg_left (D6Aux.pointwise hrn G) (hw G)
  refine le_trans (le_of_eq ?_) h2
  by_cases hA : G.IsClique (baseSet n r : Set (Fin n)) <;> simp only [hA, ↓reduceIte] <;> ring
