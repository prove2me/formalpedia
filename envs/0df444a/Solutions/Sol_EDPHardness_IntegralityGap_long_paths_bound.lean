-- Prove2me | solution 1 for EDPHardness.IntegralityGap.long_paths_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:08:24.654535+00:00
-- url     : https://prove2.me/submissions/879fc64e-d96a-455b-abeb-007652304cae

import Mathlib
import Definitions.Def_EDPHardness_IntegralityGap_FlowRelaxation
import Definitions.Def_EDPHardness_IntegralityGap_GapInstance

namespace EDPLongBoundAux

open EDPHardness.IntegralityGap

variable {n m c : ℕ}

/-- hyperedges containing `v` -/
def Fv (H : Hyp n m c) (v : Fin n) : Finset (Fin m) := Finset.univ.filter (fun j => v ∈ (H j).1)

/-- hyperedges containing `v` after `a` -/
def Nva (H : Hyp n m c) (v : Fin n) (a : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun j => a < j ∧ v ∈ (H j).1)

noncomputable def firstEdge (H : Hyp n m c) (v : Fin n) : Sym2 (Node n m) :=
  if h : (Fv H v).Nonempty then s(Node.s v, Node.l ((Fv H v).min' h)) else s(Node.s v, Node.t v)

noncomputable def lastEdge (H : Hyp n m c) (v : Fin n) : Sym2 (Node n m) :=
  if h : (Fv H v).Nonempty then s(Node.r ((Fv H v).max' h), Node.t v) else s(Node.s v, Node.t v)

noncomputable def consEdge (H : Hyp n m c) (p : Σ _a : Fin m, Fin n) : Sym2 (Node n m) :=
  if h : (Nva H p.2 p.1).Nonempty then s(Node.r p.1, Node.l ((Nva H p.2 p.1).min' h))
  else s(Node.r p.1, Node.r p.1)

noncomputable def E0 (H : Hyp n m c) : Finset (Sym2 (Node n m)) :=
  (Finset.univ.image (fun i : Fin m => s(Node.l i, Node.r i))) ∪
  (Finset.univ.image (firstEdge H)) ∪ (Finset.univ.image (lastEdge H)) ∪
  ((Finset.univ.sigma (fun a => (H a).1)).image (consEdge H))

lemma E0_card (H : Hyp n m c) : (E0 H).card ≤ m + n + n + m * c := by
  unfold E0
  refine (Finset.card_union_le _ _).trans ?_
  refine add_le_add ((Finset.card_union_le _ _).trans (add_le_add
    ((Finset.card_union_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_
  · exact Finset.card_image_le.trans (by simp)
  · exact Finset.card_image_le.trans (by simp)
  · exact Finset.card_image_le.trans (by simp)
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_sigma]
    simp [(fun a => (H a).2)]

lemma rel_mem (H : Hyp n m c) {a b : Node n m} (h : GapRel H a b) : s(a, b) ∈ E0 H := by
  unfold E0
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  cases h with
  | special i => exact Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))
  | first v i hv hmin =>
    refine Or.inl (Or.inl (Or.inr ⟨v, ?_⟩))
    have hne : (Fv H v).Nonempty := ⟨i, by simp [Fv, hv]⟩
    have heq : (Fv H v).min' hne = i := by
      apply le_antisymm
      · exact Finset.min'_le _ _ (by simp [Fv, hv])
      · rw [Finset.le_min'_iff]
        intro y hy
        simp only [Fv, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        by_contra hlt
        exact hmin y (lt_of_not_ge hlt) hy
    simp [firstEdge, hne, heq]
  | last v i hv hmax =>
    refine Or.inl (Or.inr ⟨v, ?_⟩)
    have hne : (Fv H v).Nonempty := ⟨i, by simp [Fv, hv]⟩
    have heq : (Fv H v).max' hne = i := by
      apply le_antisymm
      · rw [Finset.max'_le_iff]
        intro y hy
        simp only [Fv, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        by_contra hlt
        exact hmax y (lt_of_not_ge hlt) hy
      · exact Finset.le_max' _ _ (by simp [Fv, hv])
    simp [lastEdge, hne, heq]
  | consec v a b hab ha hb hbetween =>
    refine Or.inr ⟨⟨a, v⟩, by simp [ha], ?_⟩
    have hne : (Nva H v a).Nonempty := ⟨b, by simp [Nva, hab, hb]⟩
    have heq : (Nva H v a).min' hne = b := by
      apply le_antisymm
      · exact Finset.min'_le _ _ (by simp [Nva, hab, hb])
      · rw [Finset.le_min'_iff]
        intro y hy
        simp only [Nva, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        by_contra hlt
        exact hbetween y hy.1 (lt_of_not_ge hlt) hy.2
    simp [consEdge, hne, heq]
  | isolated v hv =>
    refine Or.inl (Or.inl (Or.inr ⟨v, ?_⟩))
    have hne : ¬ (Fv H v).Nonempty := by
      rintro ⟨j, hj⟩
      simp only [Fv, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hv j hj
    simp [firstEdge, hne]

lemma edge_mem (H : Hyp n m c) (e : Sym2 (Node n m)) (he : e ∈ (gapGraph H).edgeSet) :
    e ∈ E0 H := by
  induction e using Sym2.ind with
  | _ a b =>
  rw [SimpleGraph.mem_edgeSet] at he
  unfold gapGraph at he
  rw [SimpleGraph.fromRel_adj] at he
  rcases he.2 with h | h
  · exact rel_mem H h
  · rw [Sym2.eq_swap]; exact rel_mem H h

end EDPLongBoundAux

open EDPHardness.IntegralityGap in
theorem solution (n c : ℕ) (hc : 2 ≤ c) (hβ₁ : 0 < beta1 n c) (hβ₂ : 1 ≤ beta2 n c)
    (H : Hyp n (numEdges n c) c)
    (R : IntRouting (gapGraph H) (src n (numEdges n c)) (snk n (numEdges n c)) (c - 1)) :
    ((Finset.univ.filter
        (fun v : R.routed => (R.path v).support ≠ canonicalSupport H v ∧
          gParam n c ≤ (R.path v).length)).card : ℝ)
      ≤ (n : ℝ) / beta1 n c := by
  classical
  set g := gParam n c with hg
  set P2 := Finset.univ.filter
    (fun v : R.routed => (R.path v).support ≠ canonicalSupport H v ∧ g ≤ (R.path v).length)
  set E := EDPLongBoundAux.E0 H
  -- total length bound
  have hlen : ∀ w : R.routed, (R.path w).length =
      ∑ e ∈ E, if e ∈ (R.path w).edges then 1 else 0 := by
    intro w
    have hnd : (R.path w).edges.Nodup :=
      SimpleGraph.Walk.edges_nodup_of_support_nodup ((R.isPath w).support_nodup)
    have hsub : (R.path w).edges.toFinset ⊆ E := by
      intro e he
      rw [List.mem_toFinset] at he
      exact EDPLongBoundAux.edge_mem H e (SimpleGraph.Walk.edges_subset_edgeSet (R.path w) he)
    rw [← SimpleGraph.Walk.length_edges, ← List.toFinset_card_of_nodup hnd,
      Finset.sum_boole]
    simp only [Nat.cast_id]
    congr 1
    ext e
    simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun h => ⟨hsub (List.mem_toFinset.2 h), h⟩, fun h => h.2⟩
  have htot : ∑ w : R.routed, (R.path w).length ≤ (c - 1) * E.card := by
    rw [Finset.sum_congr rfl (fun w _ => hlen w), Finset.sum_comm]
    calc _ ≤ ∑ _e ∈ E, (c - 1) := by
          apply Finset.sum_le_sum
          intro e _
          rw [Finset.sum_boole]
          simpa using R.congestion e
      _ = (c - 1) * E.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hP2 : P2.card * g ≤ ∑ w : R.routed, (R.path w).length := by
    calc P2.card * g = ∑ _w ∈ P2, g := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ w ∈ P2, (R.path w).length := by
          apply Finset.sum_le_sum
          intro w hw
          simp only [P2, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          exact hw.2
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hE := EDPLongBoundAux.E0_card H
  have key : P2.card * g ≤ (c - 1) * (numEdges n c + n + n + numEdges n c * c) :=
    hP2.trans (htot.trans (Nat.mul_le_mul_left _ hE))
  -- real arithmetic
  have hmR : (numEdges n c : ℝ) ≤ beta2 n c * n := by
    unfold numEdges
    exact Nat.floor_le (by positivity)
  have hgR : 3 * beta1 n c * beta2 n c * (c : ℝ) ^ 2 ≤ g := by
    rw [hg]; unfold gParam; exact Nat.le_ceil _
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hc1 : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have keyR : (P2.card : ℝ) * g ≤ ((c : ℝ) - 1) * (numEdges n c + n + n + numEdges n c * c) := by
    have := (Nat.cast_le (α := ℝ)).2 key
    push_cast [Nat.cast_sub (show 1 ≤ c by omega)] at this
    linarith
  set x : ℝ := (P2.card : ℝ)
  have hx : 0 ≤ x := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hb2 : 0 < beta2 n c := by linarith
  -- x * 3 β₁ β₂ c² ≤ (c-1)(β₂ n (c+1) + 2n) ≤ 3 β₂ c² n
  have h1 : x * (3 * beta1 n c * beta2 n c * (c : ℝ) ^ 2) ≤ x * g :=
    mul_le_mul_of_nonneg_left hgR hx
  have h2 : ((c : ℝ) - 1) * (numEdges n c + n + n + numEdges n c * c) ≤
      ((c : ℝ) - 1) * (beta2 n c * n * (c + 1) + 2 * n) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  have h3 : ((c : ℝ) - 1) * (beta2 n c * n * (c + 1) + 2 * n) ≤
      3 * beta2 n c * (c : ℝ) ^ 2 * n := by
    have : ((c : ℝ) - 1) * (beta2 n c * (c + 1) + 2) ≤ 3 * beta2 n c * (c : ℝ) ^ 2 := by
      nlinarith
    nlinarith
  have h4 : x * beta1 n c * (3 * beta2 n c * (c : ℝ) ^ 2) ≤ n * (3 * beta2 n c * (c : ℝ) ^ 2) := by
    nlinarith
  have hpos : 0 < 3 * beta2 n c * (c : ℝ) ^ 2 := by positivity
  have h5 : x * beta1 n c ≤ n := le_of_mul_le_mul_right h4 hpos
  rw [le_div_iff₀ hβ₁]
  exact h5
