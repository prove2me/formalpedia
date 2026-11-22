-- Prove2me | solution 1 for BooleanIsoperimetry.not_lowerSat_exists_minDelta_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:20.972825+00:00
-- url     : https://prove2.me/submissions/d8f59e72-5514-40db-a07c-67eb2f9372ae

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
public import Theorems.Thm_BooleanIsoperimetry_not_lowerSat_exists_minimalAbsent_maxPresent
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
    ∃ (T S : Cube N), T ∉ A ∧ S ∈ A ∧ T.card < S.card ∧
      (∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) := by
  classical
  set Q : Cube N × Cube N → Prop := fun p =>
    p.1 ∉ A ∧ p.2 ∈ A ∧ p.1.card < p.2.card with hQ
  set P : Finset (Cube N × Cube N) := Finset.univ.filter Q with hP
  have hPne : P.Nonempty := by
    obtain ⟨T, S, h1, h2, h3, h4, h5⟩ := not_lowerSat_exists_minimalAbsent_maxPresent h
    exact ⟨(T, S), by
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and, hQ]
      exact ⟨h1, h3, h5⟩⟩
  obtain ⟨p, hpP, hpmin⟩ :=
    P.exists_min_image (fun p => (p.2 \ p.1).card + (p.1 \ p.2).card) hPne
  rw [hP, Finset.mem_filter] at hpP
  obtain ⟨-, hT, hS, hcard⟩ := hpP
  refine ⟨p.1, p.2, hT, hS, hcard, ?_⟩
  intro T' S' h1 h3 h5
  have hp'P : (T', S') ∈ P := by
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and, hQ]
    exact ⟨h1, h3, h5⟩
  exact hpmin (T', S') hp'P
end BooleanIsoperimetry
