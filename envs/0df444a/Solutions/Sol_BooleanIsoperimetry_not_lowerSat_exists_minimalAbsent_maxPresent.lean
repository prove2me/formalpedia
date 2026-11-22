-- Prove2me | solution 1 for BooleanIsoperimetry.not_lowerSat_exists_minimalAbsent_maxPresent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:26.730964+00:00
-- url     : https://prove2.me/submissions/e36a4c25-e033-4f4d-b408-d329c651d275

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
public import Theorems.Thm_BooleanIsoperimetry_not_lowerLevelSaturated_exists_witness
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
    (h : ¬ IsLowerLevelSaturated A) :
    ∃ (T S : Cube N), T ∉ A ∧ (∀ R : Cube N, R ⊂ T → R ∈ A) ∧
      S ∈ A ∧ (∀ R ∈ A, R.card ≤ S.card) ∧ T.card < S.card := by
  classical
  -- A raw witness of saturation failure.
  obtain ⟨T₀, S₀, hT₀, hS₀, hcard₀⟩ := not_lowerLevelSaturated_exists_witness h
  -- A maximum-cardinality present block.
  obtain ⟨S, hSA, hSmax⟩ :
      ∃ S ∈ A, ∀ R ∈ A, R.card ≤ S.card :=
    A.exists_max_image (fun R => R.card) ⟨S₀, hS₀⟩
  have hS0_le : S₀.card ≤ S.card := hSmax S₀ hS₀
  -- A ⊆-minimal absent block contained in T₀ (so all its proper subsets lie in A).
  set B := T₀.powerset.filter (fun R => R ∉ A) with hBdef
  have hT0B : T₀ ∈ B := by
    simp only [hBdef, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, hT₀⟩
  obtain ⟨T, hTB, hTmin⟩ := B.exists_min_image (fun R => R.card) ⟨T₀, hT0B⟩
  rw [hBdef, Finset.mem_filter, Finset.mem_powerset] at hTB
  obtain ⟨hTsub, hTA⟩ := hTB
  refine ⟨T, S, hTA, ?_, hSA, hSmax, ?_⟩
  · -- every proper subset of `T` is present, by ⊆-minimality of `T` among absent subsets of `T₀`.
    intro R hR
    by_contra hRA
    have hRB : R ∈ B := by
      simp only [hBdef, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨(hR.subset).trans hTsub, hRA⟩
    have hle := hTmin R hRB
    have hlt : R.card < T.card := Finset.card_lt_card hR
    omega
  · have hTcard : T.card ≤ T₀.card := Finset.card_le_card hTsub
    omega
end BooleanIsoperimetry
