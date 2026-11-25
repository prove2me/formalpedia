-- Prove2me | solution 1 for ErdosPosa.moore
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:25:40.01132+00:00
-- url     : https://prove2.me/submissions/bb7a3edb-d0c4-43a5-aef1-9513165d778e

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Definitions.Def_ErdosPosaLib_EPMoore
public import Theorems.Thm_ErdosPosa_dist_adj_le
public import Theorems.Thm_ErdosPosa_moore_parent_unique
public import Theorems.Thm_ErdosPosa_moore_no_same_level
public import Theorems.Thm_ErdosPosa_deg_eq_card
public import Theorems.Thm_ErdosPosa_MinCyc_reachable
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*} {H : SimpleGraph V}
namespace ErdosPosa
theorem _root_.solution [Finite V] (v : V) (r : ℕ) (hdeg : ∀ x, H.Reachable v x → 3 ≤ deg H x)
    (hno : ∀ S : Set V, S.ncard ≤ 2 * r + 1 → ¬ Cyc H S) :
    2 ^ r ≤ {x | H.Reachable v x ∧ H.dist v x = r}.ncard := by
  classical
  have := Fintype.ofFinite V
  let L : ℕ → Finset V := fun d => Finset.univ.filter (fun x => H.Reachable v x ∧ H.dist v x = d)
  suffices h : ∀ d ≤ r, 2 ^ d ≤ (L d).card by
    have := h r le_rfl
    rw [← Set.ncard_coe_finset] at this
    convert this using 2
    ext; simp [L]
  intro d
  induction d with
  | zero =>
    intro _
    have : v ∈ L 0 := by simp [L]
    simpa using Finset.card_pos.2 ⟨v, this⟩
  | succ d ih =>
    intro hd
    have ih := ih (by omega)
    let C : V → Finset V := fun x =>
      Finset.univ.filter (fun y => H.Adj x y ∧ H.Reachable v y ∧ H.dist v y = d + 1)
    have hsub : (L d).biUnion C ⊆ L (d + 1) := by
      intro y hy
      simp only [Finset.mem_biUnion, C, L, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      obtain ⟨_, _, _, h1, h2⟩ := hy
      exact ⟨h1, h2⟩
    have hdisj : (↑(L d) : Set V).PairwiseDisjoint C := by
      intro x1 hx1 x2 hx2 hne
      rw [Function.onFun, Finset.disjoint_left]
      intro y hy1 hy2
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, L] at hx1 hx2
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
      exact hne (moore_parent_unique hno hd hx1.1 hx1.2 hx2.1 hx2.2 hy1.2.2 hy1.1.symm
        hy2.1.symm)
    have hC : ∀ x ∈ L d, 2 ≤ (C x).card := by
      intro x hx
      simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      let N := Finset.univ.filter (fun y => H.Adj x y)
      let P := N.filter (fun y => H.dist v y + 1 = d)
      have hN : 3 ≤ N.card := by rw [← deg_eq_card]; exact hdeg x hx.1
      have hP : P.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro y1 hy1 y2 hy2
        simp only [P, N, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
        obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
        exact moore_parent_unique hno (by omega) (hx.1.trans hy1.1.reachable)
          (by omega) (hx.1.trans hy2.1.reachable) (by omega) hx.2 hy1.1 hy2.1
      have hNsub : N ⊆ C x ∪ P := by
        intro y hy
        simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        have hry : H.Reachable v y := hx.1.trans hy.reachable
        have h1 := dist_adj_le hx.1 hy
        have h2 := dist_adj_le hry hy.symm
        simp only [C, P, N, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h3 : H.dist v y = d + 1
        · exact Or.inl ⟨hy, hry, h3⟩
        by_cases h4 : H.dist v y = d
        · exact absurd (moore_no_same_level hno (by omega) hx.1 hx.2 hry h4 hy) id
        · exact Or.inr ⟨hy, by omega⟩
      have := (Finset.card_le_card hNsub).trans (Finset.card_union_le _ _)
      omega
    calc 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      _ ≤ 2 * (L d).card := by omega
      _ = ∑ x ∈ L d, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ L d, (C x).card := Finset.sum_le_sum hC
      _ = ((L d).biUnion C).card := (Finset.card_biUnion hdisj).symm
      _ ≤ (L (d + 1)).card := Finset.card_le_card hsub
end ErdosPosa
