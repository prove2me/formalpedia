-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.comparison_of_pumpFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:01:53.988812+00:00
-- url     : https://prove2.me/submissions/7537ffab-6517-4ec6-b4f5-f95a15b16983

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Holes_Tail_prefix_drop_iff
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Holes_Tail_nil_mem_suffixDictionary
public import Theorems.Thm_DeciSigma1_Holes_Tail_mem_suffixDictionary_of_infix
public import Theorems.Thm_DeciSigma1_Holes_Tail_mem_suffixDictionary_of_suffix
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixNode_snoc
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffix_of_suffixNode_eq
public import Theorems.Thm_DeciSigma1_Holes_Tail_length_pumpFactor
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_of_lt_90a7620e9ffe
public import Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_take
public import Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_reduce_of_snoc
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_pathChannel
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_Words_mem_occurrences
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution [DecidableEq α] [DecidableEq S] {T : Table α S k} {q0 qt : S}
    {x t : List α} {ts : List (List α)} {B c c' L : ℕ}
    (hcl : NodeClosedAt T q0 (suffixDictionary ts B) x c c') (ht : t ∈ ts)
    (hfree : NoSuffixOccurrenceEndsBetween x t B c c') (hL : c' - c ≤ L) :
    T.pathChannel q0 (pumpFactor x c c' L) qt t ⊆ T.pathChannel q0 x qt t := by
  intro pq hpq
  rw [mem_pathChannel] at hpq ⊢
  obtain ⟨a, ha, b, hb, hpre, rfl⟩ := hpq
  have ⟨hcc, hc', hnode⟩ := hcl
  have hlen := length_pumpFactor (L := L) hcc hc'
  set y := pumpFactor x c c' L with hy
  set ℓ := t.length - b with hℓ
  have hu : (t.drop b).length = ℓ := by simp [hℓ]
  have hpre' := (prefix_drop_iff ha).mp hpre
  rw [hu] at hpre'
  by_cases h1 : a + ℓ ≤ c'
  · -- the occurrence ends at or before `c'`, where the pumped factor agrees with `x`
    refine ⟨a, by omega, b, hb, ?_, by rw [hy, pumpFactor_take hcc hc' hL (by omega)]⟩
    rw [prefix_drop_iff (by omega), hu]
    refine ⟨by omega, fun j hj => ?_⟩
    rw [← hpre'.2 j hj, hy, getElem?_pumpFactor_of_lt hcc hc' hL (by omega)]
  -- the occurrence ends at `a + ℓ > c'`, with the suffix node of a cut `e ∈ (c, c']` of `x`
  have hD : [] ∈ suffixDictionary ts B := nil_mem_suffixDictionary
  have hpreD : ∀ u (a : α), u ++ [a] ∈ suffixDictionary ts B → u ∈ suffixDictionary ts B :=
    fun u _ h => mem_suffixDictionary_of_infix h (List.prefix_append _ _).isInfix
  obtain ⟨e, he, hce, hen⟩ := pumpFactor_reduce_of_snoc (suffixNode T q0 (suffixDictionary ts B))
    (suffixNodeStep T (suffixDictionary ts B)) (suffixNode_snoc T q0 hD hpreD) hcc hc' hnode hL
    (a + ℓ) (by omega)
  have hce' := hce (by omega)
  have hsuf : t.drop b <:+ y.take (a + ℓ) := by
    rw [suffix_take_iff (by omega), hu]
    refine ⟨by omega, fun j hj => ?_⟩
    rw [show a + ℓ - ℓ + j = a + j by omega, hpre'.2 j hj]
  by_cases h2 : ℓ ≤ B
  · -- the compared suffix lies in the dictionary: it ends at `e` with the same state before it
    obtain ⟨hpx, hst⟩ := suffix_of_suffixNode_eq T q0 hen hsuf
      (mem_suffixDictionary_of_suffix ht (List.drop_suffix b t) (by omega))
    simp only [List.length_take, hu, List.take_take] at hst
    rw [min_eq_left (by omega : e ≤ x.length), min_eq_left (by omega : a + ℓ ≤ y.length),
      min_eq_left (by omega : e - ℓ ≤ e), min_eq_left (by omega : a + ℓ - ℓ ≤ a + ℓ),
      show a + ℓ - ℓ = a by omega] at hst
    rw [suffix_take_iff (by omega), hu] at hpx
    refine ⟨e - ℓ, by omega, b, hb, ?_, by rw [hst]⟩
    rw [prefix_drop_iff (by omega), hu]
    exact ⟨by omega, fun j hj => hpx.2 j hj⟩
  · -- the suffix of length `B` of the target would end inside `(c, c']`
    exfalso
    have hBt : B ≤ t.length := by omega
    have hv : Words.suffixOfLength t B <:+ y.take (a + ℓ) :=
      (List.suffix_of_suffix_length_le (List.drop_suffix _ t) (List.drop_suffix b t)
        (by simp; omega)).trans hsuf
    obtain ⟨hvx, -⟩ := suffix_of_suffixNode_eq T q0 hen hv
      (mem_suffixDictionary_of_suffix ht (List.drop_suffix _ t) (by simp))
    have hocc : e ∈ Words.occurrences x t B :=
      Words.mem_occurrences.mpr ⟨by omega, hBt, hvx⟩
    rcases hfree _ hocc with h | h <;> omega
end DeciSigma1.Holes.Tail
