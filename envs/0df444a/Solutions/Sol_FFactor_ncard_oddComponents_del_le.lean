-- Prove2me | solution 1 for FFactor.ncard_oddComponents_del_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:54:53.990033+00:00
-- url     : https://prove2.me/submissions/7ae562a7-758f-4226-af78-166ce7c91724

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Theorems.Thm_FFactor_label_eq_of_reachable
public import Theorems.Thm_FFactor_mem_del_verts
public import Theorems.Thm_FFactor_delIncl_injective
attribute [local simp] FFactor.mem_del_verts

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {W : Type*} (Γ : SimpleGraph W)
namespace FFactor
theorem _root_.solution [Finite W] (U : Set W) (x : W) (hx : x ∈ U)
    (h3 : ∀ a b c : ((⊤ : Γ.Subgraph).deleteVerts U).verts, Γ.Adj x a → Γ.Adj x b →
      Γ.Adj x c → (del Γ U).Reachable a b ∨ (del Γ U).Reachable a c ∨
        (del Γ U).Reachable b c) :
    (del Γ U).oddComponents.ncard ≤ (del Γ (U \ {x})).oddComponents.ncard + 1 := by
  classical
  set H := del Γ U
  set H' := del Γ (U \ {x})
  let ι := delIncl Γ U x
  let A : Set H.ConnectedComponent :=
    {c | ∃ a : ((⊤ : Γ.Subgraph).deleteVerts U).verts, c = H.connectedComponentMk a ∧ Γ.Adj x a}
  let B : Set H.ConnectedComponent := {c | c ∉ A ∧ Odd c.supp.ncard}
  -- `A` has at most two elements
  have hA : A.ncard ≤ 2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2, c3, h1, h2, h3', h12, h13, h23⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).mp hcon
    obtain ⟨a1, rfl, ha1⟩ := h1
    obtain ⟨a2, rfl, ha2⟩ := h2
    obtain ⟨a3, rfl, ha3⟩ := h3'
    rcases h3 a1 a2 a3 ha1 ha2 ha3 with h | h | h
    · exact h12 (ConnectedComponent.sound h)
    · exact h13 (ConnectedComponent.sound h)
    · exact h23 (ConnectedComponent.sound h)
  have hsub : H.oddComponents ⊆ B ∪ A := by
    intro c hc
    by_cases hcA : c ∈ A
    · exact Or.inr hcA
    · exact Or.inl ⟨hcA, hc⟩
  have hodd1 : H.oddComponents.ncard ≤ B.ncard + 2 :=
    (Set.ncard_le_ncard hsub).trans ((Set.ncard_union_le _ _).trans (by omega))
  -- the label on `H'`
  let ψ : ((⊤ : Γ.Subgraph).deleteVerts (U \ {x})).verts → Option H.ConnectedComponent :=
    fun y => if h : y.1 ∉ U then
      (if H.connectedComponentMk ⟨y.1, by simpa using h⟩ ∈ A then none
        else some (H.connectedComponentMk ⟨y.1, by simpa using h⟩)) else none
  have hψι : ∀ a, H.connectedComponentMk a ∉ A → ψ (ι a) = some (H.connectedComponentMk a) := by
    intro a ha
    have h' : (a : W) ∉ U := a.2.2
    have e : ψ (ι a) = if H.connectedComponentMk a ∈ A then none
        else some (H.connectedComponentMk a) := dif_pos h'
    rw [e, if_neg ha]
  have hψ1 : ∀ y z, H'.Adj y z → ψ y = ψ z := by
    have key : ∀ y z : ((⊤ : Γ.Subgraph).deleteVerts (U \ {x})).verts, H'.Adj y z →
        (y : W) ∈ U → ψ y = ψ z := by
      intro y z hyz hy
      have hyx : (y : W) = x := by have := y.2; simp_all
      have hy' : ψ y = none := by simp [ψ, hy]
      rw [hy']
      by_cases hz : (z : W) ∈ U
      · simp [ψ, hz]
      · have hmem : H.connectedComponentMk ⟨z.1, by simpa using hz⟩ ∈ A :=
          ⟨⟨z.1, by simpa using hz⟩, rfl, hyx ▸ (del_adj Γ (U := U \ {x})).mp hyz⟩
        simp [ψ, hz, hmem]
    intro y z hyz
    by_cases hy : (y : W) ∈ U
    · exact key y z hyz hy
    by_cases hz : (z : W) ∈ U
    · exact (key z y hyz.symm hz).symm
    have hc : H.connectedComponentMk ⟨y.1, by simpa using hy⟩ =
        H.connectedComponentMk ⟨z.1, by simpa using hz⟩ :=
      ConnectedComponent.connectedComponentMk_eq_of_adj
        ((del_adj Γ (U := U)).mpr ((del_adj Γ (U := U \ {x})).mp hyz))
    simp only [ψ, hy, hz, not_false_eq_true, dite_true, hc]
  have hBle : B.ncard ≤ H'.oddComponents.ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun c => c.map ι)
    · intro c hc
      obtain ⟨hcA, hcodd⟩ := hc
      induction c using ConnectedComponent.ind with | h a => ?_
      change Odd (H'.connectedComponentMk (ι a)).supp.ncard
      have hsupp : (H'.connectedComponentMk (ι a)).supp = ι '' (H.connectedComponentMk a).supp := by
        ext z
        simp only [ConnectedComponent.mem_supp_iff, Set.mem_image]
        constructor
        · intro hz
          have hzψ : ψ z = some (H.connectedComponentMk a) := by
            rw [← hψι a hcA]
            exact label_eq_of_reachable H' ψ hψ1 (ConnectedComponent.exact hz)
          have hzU : (z : W) ∉ U := by
            intro h; simp [ψ, h] at hzψ
          refine ⟨⟨z.1, by simpa using hzU⟩, ?_, rfl⟩
          simp only [ψ, hzU, not_false_eq_true, dite_true] at hzψ
          split_ifs at hzψ
          exact Option.some_injective _ hzψ
        · rintro ⟨b, hb, rfl⟩
          rw [← ConnectedComponent.map_mk, ← ConnectedComponent.map_mk, hb]
      rw [hsupp, Set.ncard_image_of_injective _ (delIncl_injective Γ U x)]
      exact hcodd
    · intro c hc d hd hcd
      induction c using ConnectedComponent.ind with | h a => ?_
      induction d using ConnectedComponent.ind with | h b => ?_
      have hr : H'.Reachable (ι a) (ι b) := by
        apply ConnectedComponent.exact
        exact hcd
      have := label_eq_of_reachable H' ψ hψ1 hr
      rw [hψι a hc.1, hψι b hd.1] at this
      exact Option.some_injective _ this
  -- parity
  have hcard : Nat.card ((⊤ : Γ.Subgraph).deleteVerts (U \ {x})).verts =
      Nat.card ((⊤ : Γ.Subgraph).deleteVerts U).verts + 1 := by
    simp only [Nat.card_coe_set_eq, Subgraph.deleteVerts_verts, Subgraph.verts_top]
    rw [show Set.univ \ (U \ {x}) = insert x (Set.univ \ U) by
      ext y; by_cases hy : y = x <;> simp [hy, hx]]
    rw [Set.ncard_insert_of_notMem (by simp [hx])]
  have hp1 := (odd_ncard_oddComponents H)
  have hp2 := (odd_ncard_oddComponents H')
  rw [hcard] at hp2
  simp only [Nat.odd_iff] at hp1 hp2
  have hpar : H'.oddComponents.ncard % 2 ≠ H.oddComponents.ncard % 2 := by
    omega
  omega
end FFactor
