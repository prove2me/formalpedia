-- Prove2me | solution 1 for BeckFialaMatrix.exists_step_along
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:56:06.109228+00:00
-- url     : https://prove2.me/submissions/2fbb8212-1a98-4e7c-bb4d-60e10c453341

module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Definitions.Def_LeanPool_BeckFialaMatrix_Basic

set_option autoImplicit true
@[expose] public section
public section
open Finset
open BeckFialaMatrix
variable {m N : ℕ}
namespace BeckFialaMatrix
theorem _root_.solution (x : Fin N → ℚ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (F : Finset (Fin N)) (hF : ∀ i ∈ F, 0 < x i ∧ x i < 1)
    (v : Fin N → ℚ) (hv0 : ∀ i ∉ F, v i = 0) (i0 : Fin N) (hi0 : i0 ∈ F) (hvi0 : v i0 ≠ 0) :
    ∃ s : ℚ, 0 < s ∧ (∀ i, 0 ≤ x i + s * v i ∧ x i + s * v i ≤ 1) ∧
      ∃ i ∈ F, x i + s * v i = 0 ∨ x i + s * v i = 1 := by
  classical
  set G := F.filter (fun i => v i ≠ 0) with hG
  have hGne : G.Nonempty := ⟨i0, by simp [hG, hi0, hvi0]⟩
  set b : Fin N → ℚ := fun i => if 0 < v i then (1 - x i) / v i else (-x i) / v i with hb
  set s := G.inf' hGne b with hsdef
  have hmemG : ∀ i ∈ G, i ∈ F ∧ v i ≠ 0 := by
    intro i hi; simpa [hG] using mem_filter.mp hi
  have hbpos : ∀ i ∈ G, 0 < b i := by
    intro i hi
    obtain ⟨hiF, hvne⟩ := hmemG i hi
    obtain ⟨h0, h1⟩ := hF i hiF
    by_cases hv : 0 < v i
    · simp only [hb, if_pos hv]
      exact div_pos (by linarith) hv
    · have hvneg : v i < 0 := lt_of_le_of_ne (not_lt.mp hv) hvne
      simp only [hb, if_neg hv]
      exact div_pos_of_neg_of_neg (by linarith) hvneg
  have hs : 0 < s := (Finset.lt_inf'_iff hGne).mpr hbpos
  have hsle : ∀ i ∈ G, s ≤ b i := fun i hi => Finset.inf'_le b hi
  have hrange : ∀ i, 0 ≤ x i + s * v i ∧ x i + s * v i ≤ 1 := by
    intro i
    by_cases hvz : v i = 0
    · simpa only [hvz, mul_zero, add_zero] using hx i
    · have hiF : i ∈ F := by by_contra h; exact hvz (hv0 i h)
      have hiG : i ∈ G := by simp [hG, hiF, hvz]
      obtain ⟨h0, h1⟩ := hF i hiF
      have hle := hsle i hiG
      by_cases hv : 0 < v i
      · simp only [hb, if_pos hv] at hle
        have : s * v i ≤ 1 - x i := (le_div_iff₀ hv).mp hle
        have hpos : 0 < s * v i := mul_pos hs hv
        constructor <;> linarith
      · have hvneg : v i < 0 := lt_of_le_of_ne (not_lt.mp hv) hvz
        simp only [hb, if_neg hv] at hle
        have : -x i ≤ s * v i := (le_div_iff_of_neg hvneg).mp hle
        have hneg : s * v i < 0 := mul_neg_of_pos_of_neg hs hvneg
        constructor <;> linarith
  obtain ⟨i1, hi1G, hi1eq⟩ := Finset.exists_mem_eq_inf' hGne b
  obtain ⟨hi1F, hi1v⟩ := hmemG i1 hi1G
  refine ⟨s, hs, hrange, i1, hi1F, ?_⟩
  by_cases hv : 0 < v i1
  · right
    rw [hsdef, hi1eq]
    simp only [hb, if_pos hv]
    field_simp
    ring
  · left
    rw [hsdef, hi1eq]
    simp only [hb, if_neg hv]
    field_simp
    ring
end BeckFialaMatrix
