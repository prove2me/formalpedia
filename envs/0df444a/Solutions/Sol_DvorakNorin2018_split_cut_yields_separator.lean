-- Prove2me | solution 1 for DvorakNorin2018.split_cut_yields_separator
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T17:08:47.857212+00:00
-- url     : https://prove2.me/submissions/afa85cf5-ecba-4225-99e6-e39aacce0552

import Definitions.Def_DvorakNorin2018_SplitNetwork
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.BigOperators.Ring.Finset
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators
namespace StableMSR.Recovery.SplitNetwork
open TreewidthApprox.Pushed
lemma sum_nodes {V : Type} [Fintype V] (f : Node V → ℝ) :
    (∑ x, f x) = f source + f sink + (∑ v, f (input v)) + ∑ v, f (output v) := by
  simp only [Node, Fintype.sum_sum_type, Fintype.sum_unique, source, sink, input, output]
  <;> simp only [add_assoc]
lemma capacity_nonneg {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) (hα : 0 ≤ α) (hM : 0 ≤ M) (x y : Node V) :
    0 ≤ capacity G W α M x y := by
  rcases x with u | (u | (v | v)) <;> rcases y with w | (w | (z | z)) <;>
    simp only [capacity] <;> (try split_ifs) <;> positivity
lemma row_nonneg {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) (hα : 0 ≤ α) (hM : 0 ≤ M) (C : Finset (Node V)) (x : Node V) :
    0 ≤ row G W α M C x := by
  unfold row
  split_ifs
  · exact Finset.sum_nonneg (fun y _ => by by_cases h : y ∉ C <;> simp only [h, ite_true, ite_false]; exact capacity_nonneg G W α M hα hM x y; rfl)
  · rfl
lemma entry_le_cut {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) (hα : 0 ≤ α) (hM : 0 ≤ M) (C : Finset (Node V))
    (x y : Node V) (hx : x ∈ C) (hy : y ∉ C) : capacity G W α M x y ≤ cut G W α M C := by
  have h₁ : capacity G W α M x y ≤ row G W α M C x := by
    unfold row
    rw [if_pos hx]
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun z => if z ∉ C then capacity G W α M x z else 0)
      (fun z _ => by by_cases h : z ∉ C <;> simp only [h, ite_true, ite_false]; exact capacity_nonneg G W α M hα hM x z; rfl) (Finset.mem_univ y)
    simpa only [if_pos hy] using h
  exact h₁.trans (Finset.single_le_sum (fun z _ => row_nonneg G W α M hα hM C z) (Finset.mem_univ x))
lemma source_row {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) (C : Finset (Node V)) (hs : source ∈ C) :
    row G W α M C source = ((Finset.univ.filter (fun v => input v ∉ C)).card : ℝ) := by
  unfold row
  rw [if_pos hs, sum_nodes]
  simp only [capacity, source, sink, input, output]
  simp only [ite_self, Finset.sum_const_zero, zero_add, add_zero]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_not]
lemma sink_row {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) (C : Finset (Node V)) : row G W α M C sink = 0 := by
  unfold row
  split_ifs <;> simp [sum_nodes, capacity, source, sink, input, output]
lemma input_row {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (α M : ℝ) (C : Finset (Node V)) (v : V) :
    row G W α M C (input v) = if input v ∈ C ∧ output v ∉ C then α else 0 := by
  unfold row
  by_cases hi : input v ∈ C
  · rw [if_pos hi, sum_nodes]
    simp only [capacity, source, sink, input, output, ite_self, Finset.sum_const_zero, zero_add, add_zero]
    try simp only [ite_self, Finset.sum_const_zero, zero_add, add_zero]
    have hif : ∀ w, (if output w ∉ C then if v = w then α else 0 else 0) =
        if v = w then (if output v ∉ C then α else 0) else 0 := by
      intro w; by_cases h : v = w <;> simp [h]
    change (∑ w, if output w ∉ C then if v = w then α else 0 else 0) = _
    simp_rw [hif]
    simp [hi, eq_comm]
  · simp [hi]
/-- A low-capacity split-network cut yields a separator of no greater charge. -/
theorem separator_of_cut {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α M s : ℝ) (hα : 0 ≤ α) (hM : 0 ≤ M)
    (hMs : s < M) (C : Finset (Node V)) (hsource : source ∈ C) (hsink : sink ∉ C)
    (hcut : cut G W α M C ≤ s) :
    ∃ L S R : Finset V, IsPartition3 Finset.univ L S R ∧ NoEdge G L R ∧
      W ⊆ L ∪ S ∧ (L.card : ℝ) + α * S.card ≤ s := by
  classical
  let L := Finset.univ.filter (fun v => input v ∉ C)
  let S := Finset.univ.filter (fun v => input v ∈ C ∧ output v ∉ C)
  let R := Finset.univ.filter (fun v => input v ∈ C ∧ output v ∈ C)
  have hpart : IsPartition3 Finset.univ L S R := by
    refine ⟨Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_, ?_⟩
    · intro v hv hv'; exact (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hv').2.1
    · intro v hv hv'; exact (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hv').2.1
    · intro v hv hv'; exact (Finset.mem_filter.mp hv).2.2 (Finset.mem_filter.mp hv').2.2
    · ext v; simp only [L, S, R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
  have hWout : ∀ v ∈ W, output v ∉ C := by
    intro v hv hvc
    have h := entry_le_cut G W α M hα hM C (output v) sink hvc hsink
    have hc : capacity G W α M (output v) sink = M := by simp [capacity, output, sink, hv]
    rw [hc] at h
    exact (not_le_of_gt hMs) (h.trans hcut)
  have hW : W ⊆ L ∪ S := by
    intro v hv
    by_cases hi : input v ∈ C
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hWout v hv⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have hno : NoEdge G L R := by
    intro v hv w hw hadj
    have hwi := (Finset.mem_filter.mp hw).2
    have hwW : w ∉ W := fun h => hWout w h hwi.2
    have h := entry_le_cut G W α M hα hM C (output w) (input v) hwi.2 (Finset.mem_filter.mp hv).2
    have hc : capacity G W α M (output w) (input v) = M := by
      simp [capacity, output, input, hadj.symm, hwW]
    rw [hc] at h
    exact (not_le_of_gt hMs) (h.trans hcut)
  have hrows : (∑ v, row G W α M C (input v)) = α * S.card := by
    simp_rw [input_row]
    change (∑ v, if input v ∈ C ∧ output v ∉ C then α else 0) = _
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    change (S.card : ℝ) * α = α * S.card
    exact mul_comm _ _
  have hnonneg : 0 ≤ ∑ v, row G W α M C (output v) :=
    Finset.sum_nonneg (fun v _ => row_nonneg G W α M hα hM C (output v))
  have hc : cut G W α M C = (L.card : ℝ) + α * S.card +
      ∑ v, row G W α M C (output v) := by
    rw [cut, sum_nodes, source_row G W α M C hsource, sink_row, hrows, add_zero]
  exact ⟨L, S, R, hpart, hno, hW, by linarith⟩

end StableMSR.Recovery.SplitNetwork
open TreewidthApprox.Pushed StableMSR.Recovery.SplitNetwork
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α M s : ℝ) (hα : 0 ≤ α) (hM : 0 ≤ M)
    (hMs : s < M) (C : Finset (Node V)) (hsource : source ∈ C) (hsink : sink ∉ C)
    (hcut : cut G W α M C ≤ s) :
    ∃ L S R : Finset V, IsPartition3 Finset.univ L S R ∧ NoEdge G L R ∧
      W ⊆ L ∪ S ∧ (L.card : ℝ) + α * S.card ≤ s := by
  exact separator_of_cut G W α M s hα hM hMs C hsource hsink hcut
