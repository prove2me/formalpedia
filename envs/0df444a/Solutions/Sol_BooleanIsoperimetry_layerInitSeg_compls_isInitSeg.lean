-- Prove2me | solution 1 for BooleanIsoperimetry.layerInitSeg_compls_isInitSeg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:55.273863+00:00
-- url     : https://prove2.me/submissions/25a3d591-a054-42dc-9e23-23a25ec90643

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Theorems.Thm_BooleanIsoperimetry_mem_layerInitSeg_iff
public import Theorems.Thm_BooleanIsoperimetry_toColex_lt_iff_cubeToNat_lt
public import Theorems.Thm_BooleanIsoperimetry_toColex_compl_lt_toColex_compl
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_strictMono
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N r t : ℕ} (_ : t ≤ Nat.choose N r) :
    Finset.Colex.IsInitSeg (layerInitSeg N r t)ᶜˢ (N - r) := by
  unfold Finset.Colex.IsInitSeg
  constructor
  · intro x hx
    simp only [mem_coe, mem_compls, mem_layerInitSeg_iff] at hx
    have h_card := hx.1
    have h1 : x.card + xᶜ.card = Fintype.card (Fin N) := Finset.card_add_card_compl x
    rw [Fintype.card_fin, h_card] at h1
    have h2 := Finset.card_le_univ xᶜ
    rw [Fintype.card_fin, h_card] at h2
    omega
  · rintro s u hs ⟨hlt, hcard⟩
    simp only [mem_compls, mem_layerInitSeg_iff] at hs ⊢
    have h_s_card : sᶜ.card = r := hs.1
    have hrN : r ≤ N := by
      have := Finset.card_le_univ sᶜ
      rw [Fintype.card_fin, h_s_card] at this
      exact this
    have h1 : u.card + uᶜ.card = Fintype.card (Fin N) := Finset.card_add_card_compl u
    rw [Fintype.card_fin, hcard] at h1
    have hu_card_c : uᶜ.card = r := by omega
    refine ⟨hu_card_c, ?_⟩
    have hlt_colex : toColex u < toColex s := hlt
    have h_colex_c : toColex sᶜ < toColex uᶜ := toColex_compl_lt_toColex_compl.mpr hlt_colex
    have h_c_lt : cubeToNat sᶜ < cubeToNat uᶜ := toColex_lt_iff_cubeToNat_lt.mp h_colex_c
    have h_simp : simplicialLt uᶜ sᶜ := by
      unfold simplicialLt simplicialLe
      have hc : uᶜ.card = sᶜ.card := by omega
      refine ⟨Or.inr ⟨hc, by omega⟩, ?_⟩
      rintro (h2 | ⟨h3, h4⟩)
      · omega
      · omega
    have h_rank : rank uᶜ < rank sᶜ := rank_strictMono h_simp
    omega
end BooleanIsoperimetry
