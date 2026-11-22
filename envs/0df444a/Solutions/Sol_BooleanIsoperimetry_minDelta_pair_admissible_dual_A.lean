-- Prove2me | solution 1 for BooleanIsoperimetry.minDelta_pair_admissible_dual_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:09.738215+00:00
-- url     : https://prove2.me/submissions/0bc0634b-2e8e-4346-bd10-69a0886b3696

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
public import Theorems.Thm_BooleanIsoperimetry_downFixed_sdiff_mem
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
    (hdown : IsCoordinateDownFixed A)
    (hT : T ∉ A)
    (hS : S ∈ A)
    (hcard : T.card < S.card)
    (hmin : ∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) :
    ∀ x ∈ S \ T, ∃ y ∈ T \ S, familyUp ((S \ T).erase x) ((T \ S).erase y) A = A := by
  intro y hy
  by_contra hcontra
  simp only [familyUp_eq_self_iff] at hcontra
  push Not at hcontra
  have hV_nonempty : (T \ S).Nonempty := by
    by_contra hE
    simp only [not_nonempty_iff_eq_empty] at hE
    have h_sub : T ⊆ S := sdiff_eq_empty_iff_subset.mp hE
    have h_T_eq : S \ (S \ T) = T := Finset.sdiff_sdiff_eq_self h_sub
    have h_in_A : T ∈ A := by
      have h1 : S \ (S \ T) ∈ A := downFixed_sdiff_mem hdown hS sdiff_subset
      rwa [h_T_eq] at h1
    exact hT h_in_A
  obtain ⟨x, hx⟩ := hV_nonempty
  obtain ⟨Rx, hRxA, hRx_sub, hRx_disj, hRx_notin⟩ := hcontra x hx
  let Uy := (S \ T).erase y
  let Vx := (T \ S).erase x
  let Tx := blockReplace Uy Vx Rx
  have hd : Disjoint (Rx \ Uy) Vx := Disjoint.symm (Disjoint.mono_right sdiff_subset hRx_disj)
  have hx_pos : 0 < (T \ S).card := card_pos.mpr ⟨x, hx⟩
  have hy_pos : 0 < (S \ T).card := card_pos.mpr ⟨y, hy⟩
  have hUy_card : Uy.card = (S \ T).card - 1 := card_erase_of_mem hy
  have hVx_card : Vx.card = (T \ S).card - 1 := card_erase_of_mem hx
  have hRx_eq : Rx.card = (Rx \ Uy).card + Uy.card := by
    exact (card_sdiff_add_card_eq_card hRx_sub).symm
  have hTx_eq : Tx.card = (Rx \ Uy).card + Vx.card := by
    have hd_union : Disjoint (Rx \ Uy) Vx := hd
    exact card_union_of_disjoint hd_union
  have h_diff : (T \ S).card < (S \ T).card := by
    have hS_eq := card_sdiff_add_card_inter S T
    have hT_eq := card_sdiff_add_card_inter T S
    rw [inter_comm] at hT_eq
    omega
  have hTx_card : Tx.card < Rx.card := by omega
  have h_hmin := hmin Tx Rx hRx_notin hRxA hTx_card
  have h_Rx_Tx : (Rx \ Tx).card = Uy.card := by
    have h1 : Rx \ Tx = Uy := by
      ext a
      simp only [Tx, blockReplace, mem_sdiff, mem_union]
      constructor
      · intro h
        have ha_Rx := h.1
        have ha_not_Tx := h.2
        push Not at ha_not_Tx
        have ha_not_Rx_Uy := ha_not_Tx.1
        by_contra h_not_Uy
        exact h_not_Uy (ha_not_Rx_Uy ha_Rx)
      · intro ha_Uy
        have ha_Rx : a ∈ Rx := hRx_sub ha_Uy
        have ha_not_Rx_Uy : ¬(a ∈ Rx ∧ a ∉ Uy) := by
          intro h; exact h.2 ha_Uy
        have ha_not_Vx : a ∉ Vx := by
          have hd1 : Disjoint Uy Vx :=
            Disjoint.mono (erase_subset y (S \ T)) (erase_subset x (T \ S)) disjoint_sdiff_sdiff
          exact disjoint_left.mp hd1 ha_Uy
        exact ⟨ha_Rx, fun h => h.elim ha_not_Rx_Uy ha_not_Vx⟩
    rw [h1]
  have h_Tx_Rx : (Tx \ Rx).card = Vx.card := by
    have h1 : Tx \ Rx = Vx := by
      ext a
      simp only [Tx, blockReplace, mem_sdiff, mem_union]
      constructor
      · intro h
        have ha_Tx := h.1
        have ha_not_Rx := h.2
        cases ha_Tx with
        | inl hRx_Uy => exact False.elim (ha_not_Rx hRx_Uy.1)
        | inr hVx => exact hVx
      · intro ha_Vx
        have ha_not_Rx : a ∉ Rx := by
          exact disjoint_left.mp hRx_disj ha_Vx
        exact ⟨Or.inr ha_Vx, ha_not_Rx⟩
    rw [h1]
  omega
end BooleanIsoperimetry
