-- Prove2me | solution 1 for ExplicitExpanders.Delete.theorem_1_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:48:22.591168+00:00
-- url     : https://prove2.me/submissions/87cd2a00-ebbf-4b16-b6a5-543bc2ecc0f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
import Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch
import Theorems.Thm_ExplicitExpanders_Delete_lemma_3_1
import Theorems.Thm_ExplicitExpanders_Delete_spectral_step

set_option autoImplicit false

namespace ExplicitExpanders.Delete

theorem rd5734_exists_matching_of_even {V : Type*} [DecidableEq V] :
    ∀ (k : ℕ) (S : Finset V), S.card = 2 * k → ∃ m : V → V, IsMatchingOn S m := by
  intro k
  induction k with
  | zero =>
    intro S hS
    refine ⟨id, ?_⟩
    intro x hx
    have h0 : S = ∅ := Finset.card_eq_zero.1 (by simpa using hS)
    subst h0
    simp at hx
  | succ k ih =>
    intro S hS
    obtain ⟨a, ha⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
    have h1 : (S.erase a).card = 2 * k + 1 := by rw [Finset.card_erase_of_mem ha]; omega
    obtain ⟨b, hb⟩ : (S.erase a).Nonempty := Finset.card_pos.1 (by omega)
    have hba : b ≠ a := Finset.ne_of_mem_erase hb
    have hbS : b ∈ S := Finset.mem_of_mem_erase hb
    have h2 : ((S.erase a).erase b).card = 2 * k := by rw [Finset.card_erase_of_mem hb]; omega
    obtain ⟨m', hm'⟩ := ih _ h2
    refine ⟨fun x => if x = a then b else if x = b then a else m' x, ?_⟩
    intro x hx
    by_cases hxa : x = a
    · subst hxa
      simp [hba, hbS]
    by_cases hxb : x = b
    · subst hxb
      simp [hxa, ha, Ne.symm hxa]
    have hx' : x ∈ (S.erase a).erase b := by simp [hxa, hxb, hx]
    obtain ⟨h1, h2, h3⟩ := hm' x hx'
    have hma : m' x ≠ a := fun h => by simp [h] at h1
    have hmb : m' x ≠ b := fun h => by simp [h] at h1
    simp only [hxa, hxb, if_false, hma, hmb, h2]
    exact ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h1), by simp, h3⟩

theorem rd5734_exists_matching_nbrSet {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (hreg : H.IsRegularOfDegree d) (r : ℕ)
    (U : Finset V) (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    (heven : Even (U.card * d)) :
    ∃ m : V → V, IsMatchingOn (nbrSet H U) m := by
  have hset : nbrSet H U = U.biUnion (fun z => H.neighborFinset z) := by
    ext x; simp [nbrSet]
  have hdisj : (U : Set V).PairwiseDisjoint (fun z => H.neighborFinset z) := by
    intro z hz z' hz' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    rw [SimpleGraph.mem_neighborFinset] at hx hx'
    have hle : H.edist z z' ≤ 2 := by
      have := SimpleGraph.edist_le
        (SimpleGraph.Walk.cons hx (SimpleGraph.Walk.cons hx'.symm (SimpleGraph.Walk.nil (u := z'))))
      simpa [SimpleGraph.Walk.length_cons] using this
    have := hU3 z hz z' hz' hne
    have h3 : ((2 * r + 3 : ℕ) : ℕ∞) ≤ 2 := this.trans hle
    have : 2 * r + 3 ≤ 2 := by exact_mod_cast h3
    omega
  have hcard : (nbrSet H U).card = U.card * d := by
    rw [hset, Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl (fun z _ => (SimpleGraph.card_neighborFinset_eq_degree H z).trans (hreg z))]
    simp
  obtain ⟨k, hk⟩ := heven
  exact rd5734_exists_matching_of_even k _ (by rw [hcard, hk]; ring)

theorem rd5734_matrix_equiv {V W : Type*} [Fintype V] [Fintype W] (A : Matrix V V ℝ)
    (e : V ≃ W) {n d : ℕ} {lam : ℝ} (hA : IsNDLambdaMatrix A n d lam) :
    IsNDLambdaMatrix (A.submatrix e.symm e.symm) n d lam := by
  obtain ⟨hs, hc, h1, he⟩ := hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hs.submatrix _
  · rw [← hc]; exact (Fintype.card_congr e).symm
  · rw [Matrix.submatrix_mulVec_equiv]
    ext w
    show (A.mulVec fun _ => (1 : ℝ)) (e.symm w) = _
    rw [h1]; rfl
  · intro μ f hf hsum heig
    apply he μ (f ∘ e)
    · intro h0; apply hf; ext w; have := congrFun h0 (e.symm w); simpa using this
    · rw [← hsum]; exact Fintype.sum_equiv e _ _ (fun _ => rfl)
    · rw [Matrix.submatrix_mulVec_equiv] at heig
      ext v
      have := congrFun heig (e v)
      simpa using this

theorem rd5734_map_equiv {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (e : V ≃ W) {n d : ℕ} {lam : ℝ} (hG : IsNDLambda G n d lam) :
    IsNDLambda (G.map e.toEmbedding) n d lam := by
  classical
  obtain ⟨hreg, hM⟩ := hG
  refine ⟨?_, ?_⟩
  · intro w
    have h2 := (SimpleGraph.Iso.map e G).degree_eq (e.symm w)
    have h3 : (SimpleGraph.Iso.map e G) (e.symm w) = w := by simp [SimpleGraph.Iso.map]
    rw [h3] at h2
    convert h2.trans (hreg (e.symm w))
    all_goals rfl
  · have hmat : (G.map e.toEmbedding).adjMatrix ℝ = (G.adjMatrix ℝ).submatrix e.symm e.symm := by
      ext i j
      have hadj : (G.map e.toEmbedding).Adj i j ↔ G.Adj (e.symm i) (e.symm j) := by
        conv_lhs => rw [← e.apply_symm_apply i, ← e.apply_symm_apply j]
        exact SimpleGraph.map_adj_apply
      simp only [SimpleGraph.adjMatrix_apply, Matrix.submatrix_apply, hadj]
    convert rd5734_matrix_equiv _ e hM using 1
    convert hmat

end ExplicitExpanders.Delete

open ExplicitExpanders.Delete in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (d : ℕ) (ε : ℝ) (hd : 3 ≤ d) (hε : 0 < ε)
    (hH : IsNDLambda H (Fintype.card V) d (2 * Real.sqrt ((d : ℝ) - 1) + ε / 2))
    (hcyc : ∀ v : V, AtMostOneCycleOn H (ball H v (2 * ⌈2 / ε⌉₊ + 4)))
    (hr : (⌈2 / ε⌉₊ : ℝ) ≤ Real.logb ((d : ℝ) - 1) (Fintype.card V))
    (u : ℕ) (hu : (u : ℝ) ≤ (Fintype.card V : ℝ) / (2 * (d : ℝ) ^ (2 * ⌈2 / ε⌉₊ + 3)))
    (heven : Even (u * d)) :
    ∃ G : SimpleGraph (Fin (Fintype.card V - u)),
      IsNDLambda G (Fintype.card V - u) d (2 * Real.sqrt ((d : ℝ) - 1) + ε) := by
  classical
  have hreg : H.IsRegularOfDegree d := by
    have := hH.1; convert this
  obtain ⟨U, hUcard, hU2, hU3⟩ := lemma_3_1 H d ⌈2 / ε⌉₊ hd hreg hcyc hr
  have hu' : u ≤ U.card := by exact_mod_cast hu.trans hUcard
  obtain ⟨U', hU'U, hU'card⟩ := Finset.exists_subset_card_eq hu'
  have hU2' : ∀ z ∈ U', NoCycleOn H (ball H z (⌈2 / ε⌉₊ + 1)) := fun z hz => hU2 z (hU'U hz)
  have hU3' : ∀ z ∈ U', ∀ z' ∈ U', z ≠ z' → ((2 * ⌈2 / ε⌉₊ + 3 : ℕ) : ℕ∞) ≤ H.edist z z' :=
    fun z hz z' hz' hne => hU3 z (hU'U hz) z' (hU'U hz') hne
  obtain ⟨m, hm⟩ := rd5734_exists_matching_nbrSet H d hreg ⌈2 / ε⌉₊ U' hU3' (hU'card ▸ heven)
  have hG := spectral_step H d ε hd hε hH U' hU2' hU3' m hm
  rw [hU'card] at hG
  have hcard : Fintype.card (Kept U') = Fintype.card V - u := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hU'card]
  exact ⟨_, rd5734_map_equiv _ (Fintype.equivFinOfCardEq hcard) hG⟩
