-- Prove2me | solution 1 for DirKECC1549.Asm.residual_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-16T07:05:02.449235+00:00
-- url     : https://prove2.me/submissions/10d79752-41ea-45cb-8620-4ac026af1bf5

import Definitions.Def_DirKECC1549_Impl_FlowMath

set_option autoImplicit false

set_option autoImplicit false
open Classical Finset
open DirKECC1549.Main DirKECC1549.Main.CostAux
open DirKECC1549 DirKECC1549.Asm
variable {n m : ℕ}

theorem solution (D : Fin m → Fin n × Fin n) (u v : Fin n) (q : ℕ) (F : Finset (Fin m))
    (hF : IsUnitFlow D F u v q) (S : Finset (Fin n)) (hu : u ∈ S) (hv : v ∉ S)
    (hcl : ∀ e, (flipEdges D F e).1 ∈ S → (flipEdges D F e).2 ∈ S) : outCount D S = q := by
  -- the flow balance summed over `S`
  have hsum : ∑ x ∈ S, (((F.filter (fun e => (D e).1 = x)).card : ℤ) -
      (F.filter (fun e => (D e).2 = x)).card) = q := by
    rw [sum_congr rfl (fun x _ => hF x), sum_sub_distrib, sum_ite_eq' S u, sum_ite_eq' S v,
      if_pos hu, if_neg hv]; ring
  have hout : ∑ x ∈ S, ((F.filter (fun e => (D e).1 = x)).card : ℤ) =
      (F.filter (fun e => (D e).1 ∈ S)).card := by
    rw [card_eq_sum_card_fiberwise (s := F.filter (fun e => (D e).1 ∈ S)) (f := fun e => (D e).1)
      (t := S) (fun e he => (mem_filter.1 he).2)]
    push_cast
    apply sum_congr rfl
    intro x hx
    congr 2; ext e; simp only [mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hx⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  have hin : ∑ x ∈ S, ((F.filter (fun e => (D e).2 = x)).card : ℤ) =
      (F.filter (fun e => (D e).2 ∈ S)).card := by
    rw [card_eq_sum_card_fiberwise (s := F.filter (fun e => (D e).2 ∈ S)) (f := fun e => (D e).2)
      (t := S) (fun e he => (mem_filter.1 he).2)]
    push_cast
    apply sum_congr rfl
    intro x hx
    congr 2; ext e; simp only [mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hx⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  rw [sum_sub_distrib, hout, hin] at hsum
  -- no flow edge enters `S`; every edge leaving `S` carries flow
  have h1 : F.filter (fun e => (D e).2 ∈ S) = F.filter (fun e => (D e).1 ∈ S ∧ (D e).2 ∈ S) := by
    ext e; simp only [mem_filter]
    constructor
    · rintro ⟨he, h2⟩
      refine ⟨he, ?_, h2⟩
      have := hcl e (by simp only [flipEdges, if_pos he]; exact h2)
      simpa [flipEdges, he] using this
    · rintro ⟨he, -, h2⟩; exact ⟨he, h2⟩
  have h2 : F.filter (fun e => (D e).1 ∈ S) = F.filter (fun e => (D e).1 ∈ S ∧ (D e).2 ∈ S) ∪
      outEdges D S := by
    ext e; simp only [mem_filter, mem_union, outEdges, mem_univ, true_and]
    constructor
    · rintro ⟨he, h3⟩
      by_cases h4 : (D e).2 ∈ S
      · exact Or.inl ⟨he, h3, h4⟩
      · exact Or.inr ⟨h3, h4⟩
    · rintro (⟨he, h3, _⟩ | ⟨h3, h4⟩)
      · exact ⟨he, h3⟩
      · refine ⟨?_, h3⟩
        by_contra he
        exact h4 (by simpa [flipEdges, he] using hcl e (by simp only [flipEdges, if_neg he]; exact h3))
  have hd : Disjoint (F.filter (fun e => (D e).1 ∈ S ∧ (D e).2 ∈ S)) (outEdges D S) := by
    rw [disjoint_left]; intro e h3 h4
    simp only [mem_filter, outEdges, mem_univ, true_and] at h3 h4
    exact h4.2 h3.2.2
  rw [h1, h2, card_union_of_disjoint hd] at hsum
  unfold outCount
  push_cast at hsum
  omega
