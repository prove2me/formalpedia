-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.not_mem_closed_walk_of_noForbiddenRayOverlap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:04:18.341203+00:00
-- url     : https://prove2.me/submissions/edbd53b7-6b04-48ce-a5ed-94b1863f6f93

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Theorems.Thm_DeciSigma1_Holes_Tail_ncInv_walk
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
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
variable [Fintype ι] [DecidableEq ι] (M : StructuralReader α S k) (st : ι → S) (Ω : ι → Ray α)
  (J : ι → ℕ) (v : ι)
variable {M st Ω J v}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (hv : J v < (Ω v).onset)
    (hclean : ∀ u, u ≠ v → NoForbiddenRayOverlap (Ω v) (Ω u) (J v) (J u))
    {i : ι} {p : List ι} (hw : (raySystem M st Ω J).IsWalk (i :: p ++ [i])) : v ∉ i :: p := by
  intro hmem
  have hInvv : CandidateInvariant Ω J v v := ⟨hv, List.suffix_refl _, fun _ => rfl, Or.inl rfl⟩
  rcases List.mem_cons.mp hmem with hvi | hp
  · have hInvi : CandidateInvariant Ω J v i := by rw [← hvi]; exact hInvv
    have := ncInv_walk hclean (i :: p) i hw hInvi i List.mem_cons_self
    exact this.2 hvi.symm
  · obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hp
    have hsplit : i :: (p1 ++ v :: p2) ++ [i] = (i :: p1) ++ v :: (p2 ++ [i]) := by simp
    rw [hsplit] at hw
    have h12 := List.isChain_split.mp hw
    have hi := ncInv_walk hclean (i :: p1) v h12.1 hInvv i List.mem_cons_self
    have h2 : (raySystem M st Ω J).IsWalk ((v :: p2) ++ [i]) := by
      rw [List.cons_append]; exact h12.2
    have := ncInv_walk hclean (v :: p2) i h2 hi.1 v List.mem_cons_self
    exact this.2 rfl
end DeciSigma1.Holes.Tail
