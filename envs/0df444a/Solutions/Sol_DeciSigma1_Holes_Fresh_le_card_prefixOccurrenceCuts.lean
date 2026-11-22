-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.le_card_prefixOccurrenceCuts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:43:41.219871+00:00
-- url     : https://prove2.me/submissions/05db6bc9-0c6f-4b84-9018-ce48e871f92b

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_suffix
public import Theorems.Thm_DeciSigma1_Holes_Fresh_length_marker_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_marker_succ
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
open DeciSigma1.Readers.Table
variable {S : Type} [Fintype S] [DecidableEq S]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t : ℕ} (ht : 1 ≤ t) :
    ∀ l ∈ active W t, t ≤ (prefixOccurrenceCuts W (marker W t l)).card := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro l hl
    have hlen : (marker W 1 l).length = 1 := length_marker_one hl
    have h1 : 1 ∈ prefixOccurrenceCuts W (marker W 1 l) := by
      simp only [prefixOccurrenceCuts, mem_filter, mem_Icc, hlen]
      refine ⟨⟨le_rfl, le_rfl⟩, l, ?_⟩
      rw [List.take_of_length_le (by omega)]
      exact marker_suffix W 1 l
    exact card_pos.mpr ⟨1, h1⟩
  | succ t ht ih =>
    intro l hl
    obtain ⟨m, hm, hpre, hlt, -⟩ := contextAnchors_marker_succ ht hl
    have hsub : insert (marker W (t + 1) l).length (prefixOccurrenceCuts W (marker W t m)) ⊆
        prefixOccurrenceCuts W (marker W (t + 1) l) := by
      intro p hp
      simp only [prefixOccurrenceCuts, mem_insert, mem_filter, mem_Icc] at hp ⊢
      rcases hp with rfl | ⟨⟨hp1, hp2⟩, j, hj⟩
      · refine ⟨⟨by omega, le_rfl⟩, l, ?_⟩
        rw [List.take_length]; exact marker_suffix W (t + 1) l
      · refine ⟨⟨hp1, by omega⟩, j, ?_⟩
        rw [List.prefix_iff_eq_take.mp hpre, List.take_take, Nat.min_eq_left hp2] at hj
        exact hj
    have hnot : (marker W (t + 1) l).length ∉ prefixOccurrenceCuts W (marker W t m) := by
      simp only [prefixOccurrenceCuts, mem_filter, mem_Icc]; omega
    have := card_le_card hsub
    rw [card_insert_of_notMem hnot] at this
    have := ih m hm
    omega
end DeciSigma1.Holes.Fresh
