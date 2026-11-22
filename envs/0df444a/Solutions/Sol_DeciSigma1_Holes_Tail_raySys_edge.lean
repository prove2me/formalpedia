-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.raySys_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:02:18.910774+00:00
-- url     : https://prove2.me/submissions/b3577ad6-cee8-46ff-a2b1-adf214d7d937

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthBound_nil
attribute [local simp] DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α]
variable {ι : Type} [Fintype S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution [Fintype ι] [DecidableEq ι] {M : StructuralReader α S k} {st : ι → S}
    {Ω : ι → Ray α} {J : ι → ℕ} {i j : ι} (h : ((raySystem M st Ω J).edgeWeight i j).isSome) :
    i ≠ j ∧ ∃ a b, b ≤ J j ∧ ∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t) := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
  have hmem := Finset.mem_of_max hc
  obtain ⟨e, he, -⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_filter] at he
  obtain ⟨he, hi, hj⟩ := he
  simp only [rayEdges, Finset.mem_biUnion, Finset.mem_univ, true_and] at he
  obtain ⟨i', j', he⟩ := he
  split_ifs at he with hij
  · simp at he
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hab, -, heq⟩ := Finset.mem_filter.mp hab
    obtain ⟨-, hb⟩ := Finset.mem_product.mp hab
    simp only at hi hj
    subst hi hj
    exact ⟨hij, a, b, by have := Finset.mem_range.mp hb; omega, heq⟩
end DeciSigma1.Holes.Tail
