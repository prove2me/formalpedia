-- Prove2me | solution 1 for BooleanIsoperimetry.minDelta_pair_admissible_primal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:06.298807+00:00
-- url     : https://prove2.me/submissions/acb613df-1333-450e-abe6-96f35aa21ed5

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_familyUp_eq_self_iff
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A : Finset (Cube N)}
    {T S : Cube N}
    (_ : IsCoordinateDownFixed A)
    (_ : T ∉ A)
    (_ : S ∈ A)
    (hcard : T.card < S.card)
    (hmin : ∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) :
    ∀ x ∈ T \ S, ∃ y ∈ S \ T, familyUp ((S \ T).erase y) ((T \ S).erase x) A = A := by
  intro x hx
  by_contra hcontra
  simp only [familyUp_eq_self_iff] at hcontra
  push Not at hcontra
  have hU_nonempty : (S \ T).Nonempty := by
    by_contra hE
    simp only [not_nonempty_iff_eq_empty] at hE
    have hle : S.card ≤ T.card := by
      calc
        S.card = (S \ T).card + (S ∩ T).card := by rw [card_sdiff_add_card_inter]
        _ = 0 + (S ∩ T).card := by rw [hE, card_empty]
        _ = (T ∩ S).card := by rw [zero_add, inter_comm]
        _ ≤ T.card := Finset.card_le_card Finset.inter_subset_left
    omega
  obtain ⟨y, hy⟩ := hU_nonempty
  obtain ⟨Ry, hRyA, hRy_sub, hRy_disj, hRy_notin⟩ := hcontra y hy
  let Uy := (S \ T).erase y
  let Vx := (T \ S).erase x
  let Ty := blockReplace Uy Vx Ry
  have hd : Disjoint (Ry \ Uy) Vx := Disjoint.symm (Disjoint.mono_right sdiff_subset hRy_disj)
  have hx_pos : 0 < (T \ S).card := card_pos.mpr ⟨x, hx⟩
  have hy_pos : 0 < (S \ T).card := card_pos.mpr ⟨y, hy⟩
  have hUy_card : Uy.card = (S \ T).card - 1 := card_erase_of_mem hy
  have hVx_card : Vx.card = (T \ S).card - 1 := card_erase_of_mem hx
  have hRy_eq : Ry.card = (Ry \ Uy).card + Uy.card := by
    exact (card_sdiff_add_card_eq_card hRy_sub).symm
  have hTy_eq : Ty.card = (Ry \ Uy).card + Vx.card := by
    have hd_union : Disjoint (Ry \ Uy) Vx := hd
    exact card_union_of_disjoint hd_union
  have h_diff : (T \ S).card < (S \ T).card := by
    have hS_eq := card_sdiff_add_card_inter S T
    have hT_eq := card_sdiff_add_card_inter T S
    rw [inter_comm] at hT_eq
    omega
  have hTy_card : Ty.card < Ry.card := by omega
  have h_hmin := hmin Ty Ry hRy_notin hRyA hTy_card
  have h_Ry_Ty : (Ry \ Ty).card = Uy.card := by
    have h1 : Ry \ Ty = Uy := by
      ext a
      simp only [Ty, blockReplace, mem_sdiff, mem_union]
      constructor
      · intro h
        have ha_Ry := h.1
        have ha_not_Ty := h.2
        push Not at ha_not_Ty
        have ha_not_Ry_Uy := ha_not_Ty.1
        by_contra h_not_Uy
        exact h_not_Uy (ha_not_Ry_Uy ha_Ry)
      · intro ha_Uy
        have ha_Ry : a ∈ Ry := hRy_sub ha_Uy
        have ha_not_Ry_Uy : ¬(a ∈ Ry ∧ a ∉ Uy) := by
          intro h; exact h.2 ha_Uy
        have ha_not_Vx : a ∉ Vx := by
          have hd1 : Disjoint Uy Vx :=
            Disjoint.mono (erase_subset y (S \ T)) (erase_subset x (T \ S)) disjoint_sdiff_sdiff
          exact disjoint_left.mp hd1 ha_Uy
        exact ⟨ha_Ry, fun h => h.elim ha_not_Ry_Uy ha_not_Vx⟩
    rw [h1]
  have h_Ty_Ry : (Ty \ Ry).card = Vx.card := by
    have h1 : Ty \ Ry = Vx := by
      ext a
      simp only [Ty, blockReplace, mem_sdiff, mem_union]
      constructor
      · intro h
        have ha_Ty := h.1
        have ha_not_Ry := h.2
        cases ha_Ty with
        | inl hRy_Uy => exact False.elim (ha_not_Ry hRy_Uy.1)
        | inr hVx => exact hVx
      · intro ha_Vx
        have ha_not_Ry : a ∉ Ry := by
          exact disjoint_left.mp hRy_disj ha_Vx
        exact ⟨Or.inr ha_Vx, ha_not_Ry⟩
    rw [h1]
  omega
end BooleanIsoperimetry
