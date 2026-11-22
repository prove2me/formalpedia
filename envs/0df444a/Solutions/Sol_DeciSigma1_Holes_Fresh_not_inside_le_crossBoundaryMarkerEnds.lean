-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.not_inside_le_crossBoundaryMarkerEnds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:44:29.350023+00:00
-- url     : https://prove2.me/submissions/2a73550d-0ba1-4828-9966-e2e9680b06f8

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_reversedBlocks
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_upperSeq
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_occurrences_eq_of_nested
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_contextAnchors_succ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Holes.Fresh.length_reversedBlocks
attribute [local simp] DeciSigma1.Holes.Fresh.length_upperSeq

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} (ht : 1 ≤ t) {u z : List α}
    {p q : ℕ} (hp : p ∈ crossBoundaryMarkerEnds W t u z) (hq : q ∈ contextAnchors W t z)
        (hqp : q ≤ p) : False := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [crossBoundaryMarkerEnds, mem_filter, mem_Icc] at hp
  obtain ⟨⟨-, hpz⟩, ν, hν, hsν, hlν⟩ := hp
  obtain ⟨hqz, μ, hμ, hsμ⟩ := (mem_contextAnchors_succ W).mp hq
  have hlen : (u ++ z).length = u.length + z.length := by simp
  obtain ⟨hlν', hoν⟩ := (suffix_take_iff (by omega)).mp hsν
  have hsμ' : marker W (t + 1) μ <:+ (u ++ z).take (u.length + q) := by
    rw [List.take_length_add_append]; exact hsμ.trans (List.suffix_append _ _)
  obtain ⟨hlμ, hoμ⟩ := (suffix_take_iff (by omega)).mp hsμ'
  have hlμq : (marker W (t + 1) μ).length ≤ q := by
    have := hsμ.length_le; simp only [List.length_take] at this; omega
  obtain ⟨heq, -⟩ := marker_occurrences_eq_of_nested hν hμ hoν hoμ (by omega) (by omega)
  omega
end DeciSigma1.Holes.Fresh
