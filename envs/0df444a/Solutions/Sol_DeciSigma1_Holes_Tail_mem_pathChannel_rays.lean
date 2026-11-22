-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.mem_pathChannel_rays
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:51:53.54213+00:00
-- url     : https://prove2.me/submissions/dd7e07ec-7eb8-4f27-b7d6-6a23815f9c35

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
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_pathChannel
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_drop_streamPrefix_prefix_iff
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
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
open DeciSigma1.Arithmetic DeciSigma1.Words DeciSigma1.Automata
variable {ι : Type}
variable [DecidableEq α] [Fintype S] (M : StructuralReader α S k) [Fintype ι] [DecidableEq ι]
variable {M}
omit [Fintype S] [Fintype ι] [DecidableEq ι]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution [DecidableEq S] {st : ι → S} {Ω : ι → Ray α} {L : ι → ℕ} {i j : ι}
    {pq : S × S} :
    pq ∈ M.pathChannel (st i) (streamPrefix (Ω i).stream (L i)) (st j)
        (streamPrefix (Ω j).stream (L j)) ↔
      ∃ a ≤ L i, ∃ b ≤ L j, L j - b ≤ L i - a ∧
        (∀ t < L j - b, (Ω j).stream (b + t) = (Ω i).stream (a + t)) ∧
        pq = (rayState M (st i) (Ω i) a, rayState M (st j) (Ω j) b) := by
  rw [Table.mem_pathChannel]
  simp only [length_streamPrefix, take_streamPrefix]
  constructor
  · rintro ⟨a, ha, b, hb, hpre, rfl⟩
    rw [drop_streamPrefix_prefix_iff _ _ hb ha] at hpre
    exact ⟨a, ha, b, hb, hpre.1, hpre.2, by simp [rayState, min_eq_left ha, min_eq_left hb]⟩
  · rintro ⟨a, ha, b, hb, h1, h2, rfl⟩
    refine ⟨a, ha, b, hb, (drop_streamPrefix_prefix_iff _ _ hb ha).mpr ⟨h1, h2⟩, ?_⟩
    simp [rayState, min_eq_left ha, min_eq_left hb]
end DeciSigma1.Holes.Tail
