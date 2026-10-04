-- Prove2me | solution 1 for Conway99Formal.Norm16Attachments.SignedCells.norm16_signed_graph_weighted_capacity_cut
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T02:50:54.315978+00:00
-- url     : https://prove2.me/submissions/e9583cd6-e007-4e69-9fec-5659fff5791d

import Mathlib
import Definitions.Def_norm16_signed_attachments

set_option autoImplicit false

namespace Conway99Formal.Norm16Attachments

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem cell_sum_of_color (color : V → Fin 5) (f : V → ℤ) :
    (∑ v : V, f v) =
      (∑ x : {v : V // color v = 0}, f x.1) +
      (∑ x : {v : V // color v = 1}, f x.1) +
      (∑ x : {v : V // color v = 2}, f x.1) +
      (∑ x : {v : V // color v = 3}, f x.1) +
      (∑ x : {v : V // color v = 4}, f x.1) := by
  classical
  calc
    (∑ v : V, f v) =
        ∑ i : Fin 5, ∑ x : {v : V // color v = i}, f x.1 :=
      (Fintype.sum_fiberwise color f).symm
    _ = _ := by simp [Fin.sum_univ_succ, Fin.sum_univ_one, add_assoc]

namespace SignedCells

variable (G : SimpleGraph V) [DecidableRel G.Adj] (s : SignedCells G)

private theorem cell_ne {i j : Fin 5} (hij : i ≠ j)
    (x : Cell G s i) (y : Cell G s j) : x.1 ≠ y.1 := by
  intro hxy
  have hi : s.color y.1 = i := by simpa [hxy] using x.2
  exact hij (hi.symm.trans y.2)

private theorem adj_zero (x y : V) (h : ¬ G.Adj x y) :
    G.adjMatrix ℤ x y = 0 := by
  simp [SimpleGraph.adjMatrix_apply, h]

private theorem square_entry (h : G.IsSRGWith 99 14 1 2)
    (x y : V) (hxy : x ≠ y) :
    (∑ v : V, G.adjMatrix ℤ x v * G.adjMatrix ℤ v y) +
      G.adjMatrix ℤ x y = 2 := by
  have hcompl : Gᶜ.adjMatrix ℤ =
      (of 1 : Matrix V V ℤ) - 1 - G.adjMatrix ℤ := by
    have hh := G.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := ℤ)
    rw [G.compl_adjMatrix_eq_adjMatrix_compl ℤ] at hh
    linear_combination (norm := module) hh
  have hs : (G.adjMatrix ℤ) ^ 2 =
      12 • (1 : Matrix V V ℤ) - G.adjMatrix ℤ + 2 • (of 1 : Matrix V V ℤ) := by
    have hm := h.matrix_eq (α := ℤ)
    rw [hcompl] at hm
    rw [hm]
    module
  have he := congrArg (fun A : Matrix V V ℤ => A x y) hs
  simp only [sq, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply] at he
  simp [Matrix.one_apply, Matrix.of_apply, hxy] at he ⊢
  omega

private theorem sum_square (x y : V) :
    (∑ v : V, G.adjMatrix ℤ x v * G.adjMatrix ℤ v y) =
      (∑ u : P G s, G.adjMatrix ℤ x u.1 * G.adjMatrix ℤ u.1 y) +
      (∑ u : M G s, G.adjMatrix ℤ x u.1 * G.adjMatrix ℤ u.1 y) +
      (∑ u : Z G s, G.adjMatrix ℤ x u.1 * G.adjMatrix ℤ u.1 y) +
      (∑ u : R G s, G.adjMatrix ℤ x u.1 * G.adjMatrix ℤ u.1 y) +
      (∑ u : T G s, G.adjMatrix ℤ x u.1 * G.adjMatrix ℤ u.1 y) :=
  cell_sum_of_color s.color (fun v => G.adjMatrix ℤ x v * G.adjMatrix ℤ v y)

private theorem sum_zero_of_no_edge {i j : Fin 5}
    (x : Cell G s i) (y : Cell G s j) (k : Fin 5)
    (h : ∀ u : Cell G s k, ¬ G.Adj x.1 u.1) :
    (∑ u : Cell G s k,
      G.adjMatrix ℤ x.1 u.1 * G.adjMatrix ℤ u.1 y.1) = 0 := by
  apply Finset.sum_eq_zero
  intro u _
  rw [adj_zero G x.1 u.1 (h u)]
  simp

private theorem sum_zero_of_no_edge_right {i j : Fin 5}
    (x : Cell G s i) (y : Cell G s j) (k : Fin 5)
    (h : ∀ u : Cell G s k, ¬ G.Adj u.1 y.1) :
    (∑ u : Cell G s k,
      G.adjMatrix ℤ x.1 u.1 * G.adjMatrix ℤ u.1 y.1) = 0 := by
  apply Finset.sum_eq_zero
  intro u _
  rw [adj_zero G u.1 y.1 (h u)]
  simp

/-- P–M common R neighbors are the first exact demand matrix. -/
theorem pm (h : G.IsSRGWith 99 14 1 2) (p : P G s) (m : M G s) :
    (∑ r : R G s, G.adjMatrix ℤ p.1 r.1 * G.adjMatrix ℤ r.1 m.1) =
      2 - G.adjMatrix ℤ p.1 m.1 -
        (∑ t : T G s, G.adjMatrix ℤ p.1 t.1 * G.adjMatrix ℤ t.1 m.1) := by
  have hP := sum_zero_of_no_edge G s p m 0 (fun u =>
    s.positive_independent p.1 u.1 p.2 u.2)
  have hM := sum_zero_of_no_edge_right G s p m 1 (fun u =>
    s.negative_independent u.1 m.1 u.2 m.2)
  have hZ := sum_zero_of_no_edge G s p m 2 (fun u =>
    s.zero_anticomplete_positive p.1 u.1 p.2 u.2)
  have hs := sum_square G s p.1 m.1
  have he := square_entry G h p.1 m.1 (cell_ne G s (by decide) p m)
  rw [hP, hM, hZ] at hs
  omega

/-- P–Z common R neighbors are the second exact demand matrix. -/
theorem pz (h : G.IsSRGWith 99 14 1 2) (p : P G s) (z : Z G s) :
    (∑ r : R G s, G.adjMatrix ℤ p.1 r.1 * G.adjMatrix ℤ r.1 z.1) =
      2 - (∑ t : T G s,
        G.adjMatrix ℤ p.1 t.1 * G.adjMatrix ℤ t.1 z.1) := by
  have hP := sum_zero_of_no_edge G s p z 0 (fun u =>
    s.positive_independent p.1 u.1 p.2 u.2)
  have hM := sum_zero_of_no_edge_right G s p z 1 (fun u =>
    s.zero_anticomplete_negative u.1 z.1 u.2 z.2)
  have hZ := sum_zero_of_no_edge G s p z 2 (fun u =>
    s.zero_anticomplete_positive p.1 u.1 p.2 u.2)
  have hAdj : G.adjMatrix ℤ p.1 z.1 = 0 :=
    adj_zero G p.1 z.1 (s.zero_anticomplete_positive p.1 z.1 p.2 z.2)
  have hs := sum_square G s p.1 z.1
  have he := square_entry G h p.1 z.1 (cell_ne G s (by decide) p z)
  rw [hP, hM, hZ] at hs
  rw [hAdj] at he
  omega

/-- M–Z common R neighbors are the third exact demand matrix. -/
theorem mz (h : G.IsSRGWith 99 14 1 2) (m : M G s) (z : Z G s) :
    (∑ r : R G s, G.adjMatrix ℤ m.1 r.1 * G.adjMatrix ℤ r.1 z.1) =
      2 - (∑ t : T G s,
        G.adjMatrix ℤ m.1 t.1 * G.adjMatrix ℤ t.1 z.1) := by
  have hP := sum_zero_of_no_edge_right G s m z 0 (fun u =>
    s.zero_anticomplete_positive u.1 z.1 u.2 z.2)
  have hM := sum_zero_of_no_edge G s m z 1 (fun u =>
    s.negative_independent m.1 u.1 m.2 u.2)
  have hZ := sum_zero_of_no_edge G s m z 2 (fun u =>
    s.zero_anticomplete_negative m.1 u.1 m.2 u.2)
  have hAdj : G.adjMatrix ℤ m.1 z.1 = 0 :=
    adj_zero G m.1 z.1 (s.zero_anticomplete_negative m.1 z.1 m.2 z.2)
  have hs := sum_square G s m.1 z.1
  have he := square_entry G h m.1 z.1 (cell_ne G s (by decide) m z)
  rw [hP, hM, hZ] at hs
  rw [hAdj] at he
  omega

/-- P–T common R neighbors are the fourth exact demand matrix. -/
theorem pt (h : G.IsSRGWith 99 14 1 2) (p : P G s) (t : T G s) :
    (∑ r : R G s, G.adjMatrix ℤ p.1 r.1 * G.adjMatrix ℤ r.1 t.1) =
      2 - G.adjMatrix ℤ p.1 t.1 -
        (∑ m : M G s, G.adjMatrix ℤ p.1 m.1 * G.adjMatrix ℤ m.1 t.1) -
        (∑ u : T G s, G.adjMatrix ℤ p.1 u.1 * G.adjMatrix ℤ u.1 t.1) := by
  have hP := sum_zero_of_no_edge G s p t 0 (fun u =>
    s.positive_independent p.1 u.1 p.2 u.2)
  have hZ := sum_zero_of_no_edge G s p t 2 (fun u =>
    s.zero_anticomplete_positive p.1 u.1 p.2 u.2)
  have hs := sum_square G s p.1 t.1
  have he := square_entry G h p.1 t.1 (cell_ne G s (by decide) p t)
  rw [hP, hZ] at hs
  omega

/-- M–T common R neighbors are the fifth exact demand matrix. -/
theorem mt (h : G.IsSRGWith 99 14 1 2) (m : M G s) (t : T G s) :
    (∑ r : R G s, G.adjMatrix ℤ m.1 r.1 * G.adjMatrix ℤ r.1 t.1) =
      2 - G.adjMatrix ℤ m.1 t.1 -
        (∑ p : P G s, G.adjMatrix ℤ m.1 p.1 * G.adjMatrix ℤ p.1 t.1) -
        (∑ u : T G s, G.adjMatrix ℤ m.1 u.1 * G.adjMatrix ℤ u.1 t.1) := by
  have hM := sum_zero_of_no_edge G s m t 1 (fun u =>
    s.negative_independent m.1 u.1 m.2 u.2)
  have hZ := sum_zero_of_no_edge G s m t 2 (fun u =>
    s.zero_anticomplete_negative m.1 u.1 m.2 u.2)
  have hs := sum_square G s m.1 t.1
  have he := square_entry G h m.1 t.1 (cell_ne G s (by decide) m t)
  rw [hM, hZ] at hs
  omega

private theorem adj_nonneg (x y : V) : 0 ≤ G.adjMatrix ℤ x y := by
  by_cases h : G.Adj x y <;> simp [SimpleGraph.adjMatrix_apply, h]

private theorem r_common_nonneg (x y : V) :
    0 ≤ ∑ r : R G s,
      G.adjMatrix ℤ x r.1 * G.adjMatrix ℤ r.1 y := by
  apply Finset.sum_nonneg
  intro r _
  exact mul_nonneg (adj_nonneg G x r.1) (adj_nonneg G r.1 y)

/-- Every right-hand signed demand is nonnegative because it counts actual
common neighbors in R. -/
theorem pm_demand_nonneg (h : G.IsSRGWith 99 14 1 2)
    (p : P G s) (m : M G s) :
    0 ≤ 2 - G.adjMatrix ℤ p.1 m.1 -
      (∑ t : T G s, G.adjMatrix ℤ p.1 t.1 * G.adjMatrix ℤ t.1 m.1) := by
  rw [← pm G s h p m]
  exact r_common_nonneg G s p.1 m.1

theorem pz_demand_nonneg (h : G.IsSRGWith 99 14 1 2)
    (p : P G s) (z : Z G s) :
    0 ≤ 2 - (∑ t : T G s,
      G.adjMatrix ℤ p.1 t.1 * G.adjMatrix ℤ t.1 z.1) := by
  rw [← pz G s h p z]
  exact r_common_nonneg G s p.1 z.1

theorem mz_demand_nonneg (h : G.IsSRGWith 99 14 1 2)
    (m : M G s) (z : Z G s) :
    0 ≤ 2 - (∑ t : T G s,
      G.adjMatrix ℤ m.1 t.1 * G.adjMatrix ℤ t.1 z.1) := by
  rw [← mz G s h m z]
  exact r_common_nonneg G s m.1 z.1

theorem pt_demand_nonneg (h : G.IsSRGWith 99 14 1 2)
    (p : P G s) (t : T G s) :
    0 ≤ 2 - G.adjMatrix ℤ p.1 t.1 -
      (∑ m : M G s, G.adjMatrix ℤ p.1 m.1 * G.adjMatrix ℤ m.1 t.1) -
      (∑ u : T G s, G.adjMatrix ℤ p.1 u.1 * G.adjMatrix ℤ u.1 t.1) := by
  rw [← pt G s h p t]
  exact r_common_nonneg G s p.1 t.1

theorem mt_demand_nonneg (h : G.IsSRGWith 99 14 1 2)
    (m : M G s) (t : T G s) :
    0 ≤ 2 - G.adjMatrix ℤ m.1 t.1 -
      (∑ p : P G s, G.adjMatrix ℤ m.1 p.1 * G.adjMatrix ℤ p.1 t.1) -
      (∑ u : T G s, G.adjMatrix ℤ m.1 u.1 * G.adjMatrix ℤ u.1 t.1) := by
  rw [← mt G s h m t]
  exact r_common_nonneg G s m.1 t.1

/-- Each R vertex has exactly one neighbor of each sign. The norm16
support theorem must construct these functions and their indicator laws. -/
private theorem adj_symmetric (x y : V) :
    G.adjMatrix ℤ x y = G.adjMatrix ℤ y x := by
  simp [SimpleGraph.adjMatrix_apply, G.adj_comm]

/-- The graph P–M demand equals the sum of single-R pair contributions. -/
theorem pm_balance (h : G.IsSRGWith 99 14 1 2)
    (c : SignedNeighbors G s) (p : P G s) (m : M G s) :
    2 - G.adjMatrix ℤ p.1 m.1 -
      (∑ t : T G s, G.adjMatrix ℤ p.1 t.1 * G.adjMatrix ℤ t.1 m.1) =
      ∑ r : R G s,
        (if p = c.pos r then (1 : ℤ) else 0) *
          (if m = c.neg r then (1 : ℤ) else 0) := by
  rw [← pm G s h p m]
  apply Finset.sum_congr rfl
  intro r _
  rw [c.pos_indicator r p, adj_symmetric G r.1 m.1, c.neg_indicator r m]

/-- The graph P–Z demand equals the sum of single-R contributions. -/
theorem pz_balance (h : G.IsSRGWith 99 14 1 2)
    (c : SignedNeighbors G s) (p : P G s) (z : Z G s) :
    2 - (∑ t : T G s,
      G.adjMatrix ℤ p.1 t.1 * G.adjMatrix ℤ t.1 z.1) =
      ∑ r : R G s,
        (if p = c.pos r then (1 : ℤ) else 0) * G.adjMatrix ℤ r.1 z.1 := by
  rw [← pz G s h p z]
  apply Finset.sum_congr rfl
  intro r _
  rw [c.pos_indicator r p]

/-- The graph M–Z demand equals the sum of single-R contributions. -/
theorem mz_balance (h : G.IsSRGWith 99 14 1 2)
    (c : SignedNeighbors G s) (m : M G s) (z : Z G s) :
    2 - (∑ t : T G s,
      G.adjMatrix ℤ m.1 t.1 * G.adjMatrix ℤ t.1 z.1) =
      ∑ r : R G s,
        (if m = c.neg r then (1 : ℤ) else 0) * G.adjMatrix ℤ r.1 z.1 := by
  rw [← mz G s h m z]
  apply Finset.sum_congr rfl
  intro r _
  rw [c.neg_indicator r m]

/-- The graph P–T demand equals the sum of single-R contributions. -/
theorem pt_balance (h : G.IsSRGWith 99 14 1 2)
    (c : SignedNeighbors G s) (p : P G s) (t : T G s) :
    2 - G.adjMatrix ℤ p.1 t.1 -
      (∑ m : M G s, G.adjMatrix ℤ p.1 m.1 * G.adjMatrix ℤ m.1 t.1) -
      (∑ u : T G s, G.adjMatrix ℤ p.1 u.1 * G.adjMatrix ℤ u.1 t.1) =
      ∑ r : R G s,
        (if p = c.pos r then (1 : ℤ) else 0) * G.adjMatrix ℤ r.1 t.1 := by
  rw [← pt G s h p t]
  apply Finset.sum_congr rfl
  intro r _
  rw [c.pos_indicator r p]

/-- The graph M–T demand equals the sum of single-R contributions. -/
theorem mt_balance (h : G.IsSRGWith 99 14 1 2)
    (c : SignedNeighbors G s) (m : M G s) (t : T G s) :
    2 - G.adjMatrix ℤ m.1 t.1 -
      (∑ p : P G s, G.adjMatrix ℤ m.1 p.1 * G.adjMatrix ℤ p.1 t.1) -
      (∑ u : T G s, G.adjMatrix ℤ m.1 u.1 * G.adjMatrix ℤ u.1 t.1) =
      ∑ r : R G s,
        (if m = c.neg r then (1 : ℤ) else 0) * G.adjMatrix ℤ r.1 t.1 := by
  rw [← mt G s h m t]
  apply Finset.sum_congr rfl
  intro r _
  rw [c.neg_indicator r m]

/-- All five attachment demand coordinates, with the same signed cells. -/
theorem graphDemand_balance (h : G.IsSRGWith 99 14 1 2)
    (c : SignedNeighbors G s) (i : DemandIndex G s) :
    graphDemand G s i =
      ∑ r : R G s, graphContribution G s r (c.pos r, c.neg r) i := by
  rcases i with pm | pz | mz | pt | mt
  · rcases pm with ⟨p, m⟩
    simpa [graphDemand, graphContribution] using pm_balance G s h c p m
  · rcases pz with ⟨p, z⟩
    simpa [graphDemand, graphContribution] using pz_balance G s h c p z
  · rcases mz with ⟨m, z⟩
    simpa [graphDemand, graphContribution] using mz_balance G s h c m z
  · rcases pt with ⟨p, t⟩
    simpa [graphDemand, graphContribution] using pt_balance G s h c p t
  · rcases mt with ⟨m, t⟩
    simpa [graphDemand, graphContribution] using mt_balance G s h c m t

theorem graphDemandQ_balance (h : G.IsSRGWith 99 14 1 2)
    (c : SignedNeighbors G s) (i : DemandIndex G s) :
    graphDemandQ G s i =
      ∑ r : R G s, graphContributionQ G s r (c.pos r, c.neg r) i := by
  change (graphDemand G s i : ℚ) =
    ∑ r : R G s, (graphContribution G s r (c.pos r, c.neg r) i : ℚ)
  exact_mod_cast graphDemand_balance G s h c i

/-- The weighted capacity cut applied to all five actual graph demands.
The local-domain membership remains an explicit packet-specific hypothesis. -/
theorem graph_weighted_capacity_cut (h : G.IsSRGWith 99 14 1 2)
    (c : SignedNeighbors G s)
    (allowed : R G s → Finset (P G s × M G s))
    (hallowed : ∀ r, (c.pos r, c.neg r) ∈ allowed r)
    (weight : DemandIndex G s → ℚ) :
    (∑ i : DemandIndex G s, weight i * graphDemandQ G s i) ≤
      ∑ r : R G s, (allowed r).sup' ⟨(c.pos r, c.neg r), hallowed r⟩
        (fun pair => ∑ i : DemandIndex G s,
          weight i * graphContributionQ G s r pair i) := by
  calc
    ∑ i : DemandIndex G s, weight i * graphDemandQ G s i =
        ∑ i : DemandIndex G s, ∑ r : R G s,
          weight i * graphContributionQ G s r (c.pos r, c.neg r) i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [graphDemandQ_balance G s h c i, Finset.mul_sum]
    _ = ∑ r : R G s, ∑ i : DemandIndex G s,
          weight i * graphContributionQ G s r (c.pos r, c.neg r) i := by
            rw [Finset.sum_comm]
    _ ≤ ∑ r : R G s, (allowed r).sup' ⟨(c.pos r, c.neg r), hallowed r⟩
          (fun pair => ∑ i : DemandIndex G s,
            weight i * graphContributionQ G s r pair i) := by
            apply Finset.sum_le_sum
            intro r _
            exact Finset.le_sup'
              (fun pair => ∑ i : DemandIndex G s,
                weight i * graphContributionQ G s r pair i) (hallowed r)



end SignedCells
end Conway99Formal.Norm16Attachments

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Conway99Formal.Norm16Attachments.SignedCells G)
    (h : G.IsSRGWith 99 14 1 2)
    (c : Conway99Formal.Norm16Attachments.SignedCells.SignedNeighbors G s)
    (allowed : Conway99Formal.Norm16Attachments.SignedCells.R G s →
      Finset (Conway99Formal.Norm16Attachments.SignedCells.P G s ×
        Conway99Formal.Norm16Attachments.SignedCells.M G s))
    (hallowed : ∀ r, (c.pos r, c.neg r) ∈ allowed r)
    (weight : Conway99Formal.Norm16Attachments.SignedCells.DemandIndex G s → ℚ) :
    (∑ i : Conway99Formal.Norm16Attachments.SignedCells.DemandIndex G s,
      weight i * Conway99Formal.Norm16Attachments.SignedCells.graphDemandQ G s i) ≤
      ∑ r : Conway99Formal.Norm16Attachments.SignedCells.R G s,
        (allowed r).sup' ⟨(c.pos r, c.neg r), hallowed r⟩
          (fun pair => ∑ i : Conway99Formal.Norm16Attachments.SignedCells.DemandIndex G s,
            weight i * Conway99Formal.Norm16Attachments.SignedCells.graphContributionQ G s r pair i) := by
  exact Conway99Formal.Norm16Attachments.SignedCells.graph_weighted_capacity_cut
    G s h c allowed hallowed weight

#print axioms Conway99Formal.Norm16Attachments.SignedCells.pm
#print axioms Conway99Formal.Norm16Attachments.SignedCells.pz
#print axioms Conway99Formal.Norm16Attachments.SignedCells.mz
#print axioms Conway99Formal.Norm16Attachments.SignedCells.pt
#print axioms Conway99Formal.Norm16Attachments.SignedCells.mt
#print axioms Conway99Formal.Norm16Attachments.SignedCells.pm_demand_nonneg
#print axioms Conway99Formal.Norm16Attachments.SignedCells.pz_demand_nonneg
#print axioms Conway99Formal.Norm16Attachments.SignedCells.mz_demand_nonneg
#print axioms Conway99Formal.Norm16Attachments.SignedCells.pt_demand_nonneg
#print axioms Conway99Formal.Norm16Attachments.SignedCells.mt_demand_nonneg
#print axioms Conway99Formal.Norm16Attachments.SignedCells.pm_balance
#print axioms Conway99Formal.Norm16Attachments.SignedCells.pz_balance
#print axioms Conway99Formal.Norm16Attachments.SignedCells.mz_balance
#print axioms Conway99Formal.Norm16Attachments.SignedCells.pt_balance
#print axioms Conway99Formal.Norm16Attachments.SignedCells.mt_balance
#print axioms Conway99Formal.Norm16Attachments.SignedCells.graphDemand_balance
#print axioms Conway99Formal.Norm16Attachments.SignedCells.graphDemandQ_balance
#print axioms Conway99Formal.Norm16Attachments.SignedCells.graph_weighted_capacity_cut
#print axioms solution
