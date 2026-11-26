-- Prove2me | solution 2 for Erdos1007.nine_edges_six_minDegree_three
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T07:13:24.07109+00:00
-- url     : https://prove2.me/submissions/61f2bab5-038d-4ac4-ad7e-033890651106

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Theorems.Thm_Erdos1007_isRegularOfDegree_two_fin_six

set_option autoImplicit false

open SimpleGraph

/-- If the degree lower bound already accounts for all edge ends, it is exact everywhere. -/
private theorem regular_of_tight_degree_bound
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (lower : ∀ v, d ≤ G.degree v)
    (budget : 2 * G.edgeFinset.card ≤ Fintype.card V * d) : G.IsRegularOfDegree d := by
  have noExcess : (∑ v, (G.degree v - d)) = 0 := by
    rw [Finset.sum_tsub_distrib _ (fun v _ => lower v), G.sum_degrees_eq_twice_card_edges,
      Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ]
    exact Nat.sub_eq_zero_of_le budget
  intro v
  have hv : G.degree v - d = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => Nat.zero_le (G.degree w - d))).mp
      noExcess v (Finset.mem_univ v)
  exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hv) (lower v)

private def complementIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := (SimpleGraph.Embedding.complEquiv e.toEmbedding).map_rel_iff'

private theorem compl_two_cliques (V W : Type*) :
    ((⊤ : SimpleGraph V) ⊕g (⊤ : SimpleGraph W))ᶜ = completeBipartiteGraph V W := by
  ext x y
  cases x <;> cases y <;> simp [completeBipartiteGraph_adj]

theorem solution
    {G : SimpleGraph (Fin 6)} [DecidableRel G.Adj]
    (hE : G.edgeFinset.card = 9) (hdeg : ∀ v, 3 ≤ G.degree v) :
    Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∨
      Nonempty (Gᶜ ≃g cycleGraph 6) := by
  have cubic : G.IsRegularOfDegree 3 :=
    regular_of_tight_degree_bound hdeg (by simpa only [hE, Fintype.card_fin] using le_refl 18)
  have two : Gᶜ.IsRegularOfDegree 2 := by
    simpa only [Fintype.card_fin] using cubic.compl
  rcases Erdos1007.isRegularOfDegree_two_fin_six Gᶜ two with hexagon | triangles
  · exact Or.inr hexagon
  · obtain ⟨e⟩ := triangles
    exact Or.inl (by simpa only [compl_compl, compl_two_cliques] using
      (Nonempty.intro (complementIso e)))
