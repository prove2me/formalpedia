-- Prove2me | solution 1 for DirectedSearch.Approx.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:01:49.271863+00:00
-- url     : https://prove2.me/submissions/6f5ed46c-fa20-422d-8026-5e82819730a7

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Graphs

set_option autoImplicit false
open DirectedSearch.Approx

/-- a "depth" function on a forest: adjacent vertices have depths differing by exactly one,
and every vertex has at most one neighbour of smaller depth (its parent). -/
lemma dsa_exists_depth {V : Type} (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ d : V → ℕ, (∀ u v, G.Adj u v → d u = d v + 1 ∨ d v = d u + 1) ∧
      (∀ v a b, G.Adj v a → G.Adj v b → d a + 1 = d v → d b + 1 = d v → a = b) := by
  classical
  have hex : ∀ c : G.ConnectedComponent, ∃ r, G.connectedComponentMk r = c := fun c => c.exists_rep
  choose rc hrc using hex
  set root : V → V := fun v => rc (G.connectedComponentMk v) with hroot
  have hroot_adj : ∀ u v, G.Adj u v → root u = root v := by
    intro u v h
    simp only [hroot]
    rw [SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj h]
  have hreach : ∀ v, G.Reachable (root v) v := by
    intro v
    exact SimpleGraph.ConnectedComponent.exact (hrc _)
  refine ⟨fun v => G.dist (root v) v, ?_, ?_⟩
  · intro u v h
    have := hG.dist_eq_dist_add_one_of_adj_of_reachable (root u) h (hreach u)
    simp only [← hroot_adj u v h] at *
    exact this
  · intro v a b hva hvb ha hb
    simp only at ha hb
    have hra : root a = root v := (hroot_adj v a hva).symm
    have hrb : root b = root v := (hroot_adj v b hvb).symm
    rw [hra] at ha
    rw [hrb] at hb
    set r := root v with hr
    obtain ⟨q, hq, hql⟩ := (hreach v).exists_path_of_dist
    -- every parent lies on the shortest path q, as its penultimate vertex
    have key : ∀ c, G.Adj v c → G.dist r c + 1 = G.dist r v → c = q.penultimate := by
      intro c hvc hc
      have hrc' : G.Reachable r c := by
        have h := hreach c
        rw [← hroot_adj v c hvc] at h
        exact h
      obtain ⟨q', hq', hq'l⟩ := hrc'.exists_path_of_dist
      have hv : v ∉ q'.support := by
        intro hvm
        have h1 : G.dist r v ≤ (q'.takeUntil v hvm).length := SimpleGraph.dist_le _
        have h2 := q'.length_takeUntil_le hvm
        omega
      have hcq : c ∈ q.support :=
        hG.mem_support_of_ne_mem_support_of_adj_of_isPath hq hq' hvc hv
      exact hG.eq_penultimate_of_adj_end hq hvc hcq
    rw [key a hva ha, key b hvb hb]

/-- the edges of `G` whose deeper endpoint has depth parity `p` -/
def dsaH {V : Type} (G : SimpleGraph V) (d : V → ℕ) (p : ℕ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ((d u = d v + 1 ∧ d u % 2 = p) ∨ (d v = d u + 1 ∧ d v % 2 = p))
  symm := ⟨fun u v h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

lemma dsaH_adj {V : Type} (G : SimpleGraph V) (d : V → ℕ) (p : ℕ) (u v : V) :
    (dsaH G d p).Adj u v ↔
      G.Adj u v ∧ ((d u = d v + 1 ∧ d u % 2 = p) ∨ (d v = d u + 1 ∧ d v % 2 = p)) := Iff.rfl

lemma dsaH_le {V : Type} (G : SimpleGraph V) (d : V → ℕ) (p : ℕ) : dsaH G d p ≤ G :=
  fun _ _ h => ((dsaH_adj G d p _ _).1 h).1

lemma dsaH_star {V : Type} [Fintype V] (G : SimpleGraph V) (d : V → ℕ)
    (hP2 : ∀ v a b, G.Adj v a → G.Adj v b → d a + 1 = d v → d b + 1 = d v → a = b) (p : ℕ) :
    IsStarForest (dsaH G d p) := by
  classical
  have child : ∀ u v, (dsaH G d p).Adj u v → d u = d v + 1 → (dsaH G d p).degree u = 1 := by
    intro u v h h1
    have h' := (dsaH_adj G d p _ _).1 h
    have h2 : d u % 2 = p := by
      rcases h'.2 with ⟨_, h4⟩ | ⟨h3, _⟩
      · exact h4
      · omega
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    refine ⟨v, h, fun w hw => ?_⟩
    have hw' := (dsaH_adj G d p _ _).1 hw
    rcases hw'.2 with ⟨h3, _⟩ | ⟨h3, h4⟩
    · exact hP2 u w v hw'.1 h'.1 h3.symm h1.symm
    · omega
  intro u v h
  have h' := (dsaH_adj G d p _ _).1 h
  rcases h'.2 with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl (child u v h h1)
  · exact Or.inr (child v u h.symm h1)

lemma dsa_weight_split {V : Type} [Fintype V] (G : SimpleGraph V) (d : V → ℕ)
    (hP1 : ∀ u v, G.Adj u v → d u = d v + 1 ∨ d v = d u + 1) (wt : Sym2 V → ℝ) :
    graphWeight G wt = graphWeight (dsaH G d 0) wt + graphWeight (dsaH G d 1) wt := by
  classical
  unfold graphWeight
  have e0 : G.edgeFinset.filter (fun e => e ∈ (dsaH G d 0).edgeSet) = (dsaH G d 0).edgeFinset := by
    ext e
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    exact ⟨fun h => h.2, fun h => ⟨SimpleGraph.edgeSet_mono (dsaH_le G d 0) h, h⟩⟩
  have e1 : G.edgeFinset.filter (fun e => ¬ e ∈ (dsaH G d 0).edgeSet) = (dsaH G d 1).edgeFinset := by
    ext e
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    induction e using Sym2.ind with
    | _ u v =>
      simp only [SimpleGraph.mem_edgeSet, dsaH_adj]
      constructor
      · rintro ⟨hG, hn⟩
        refine ⟨hG, ?_⟩
        rcases hP1 u v hG with h | h
        · left; refine ⟨h, ?_⟩
          by_contra hc
          exact hn ⟨hG, Or.inl ⟨h, by omega⟩⟩
        · right; refine ⟨h, ?_⟩
          by_contra hc
          exact hn ⟨hG, Or.inr ⟨h, by omega⟩⟩
      · rintro ⟨hG, h⟩
        refine ⟨hG, ?_⟩
        rintro ⟨_, h'⟩
        rcases hP1 u v hG with h2 | h2 <;> rcases h with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
          rcases h' with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> omega
  rw [← e0, ← e1]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (wt : Sym2 V → ℝ) :
    ∃ H : SimpleGraph V, H ≤ G ∧ IsStarForest H ∧ graphWeight G wt ≤ 2 * graphWeight H wt := by
  obtain ⟨d, hP1, hP2⟩ := dsa_exists_depth G hG
  have hs := dsa_weight_split G d hP1 wt
  rcases le_total (graphWeight (dsaH G d 1) wt) (graphWeight (dsaH G d 0) wt) with h | h
  · exact ⟨dsaH G d 0, dsaH_le G d 0, dsaH_star G d hP2 0, by linarith⟩
  · exact ⟨dsaH G d 1, dsaH_le G d 1, dsaH_star G d hP2 1, by linarith⟩
