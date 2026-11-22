-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.ncInv_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:32.780295+00:00
-- url     : https://prove2.me/submissions/f77249ef-fbe2-4578-b458-5324bf54fc79

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Theorems.Thm_DeciSigma1_Holes_Tail_raySys_edge
public import Theorems.Thm_DeciSigma1_Holes_Tail_ncInv_step
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_isWalk_cons_cons
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
variable [Fintype ι] [DecidableEq ι] (M : StructuralReader α S k) (st : ι → S) (Ω : ι → Ray α)
  (J : ι → ℕ) (v : ι)
variable {M st Ω J v}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (hclean : ∀ u, u ≠ v → NoForbiddenRayOverlap (Ω v) (Ω u) (J v) (J u)) :
    ∀ (ys : List ι) (y : ι), (raySystem M st Ω J).IsWalk (ys ++ [y]) → CandidateInvariant Ω J v y →
      ∀ z ∈ ys, CandidateInvariant Ω J v z ∧ z ≠ v
  | [], _, _, _ => by simp
  | z :: zs, y, hw, hy => by
    have hw' : (raySystem M st Ω J).IsWalk (z :: (zs ++ [y])) := by simpa using hw
    have ih := solution hclean zs y (by
      cases zs with
      | nil => simp [DifferenceSystem.IsWalk]
      | cons w ws =>
        rw [List.cons_append, DifferenceSystem.isWalk_cons_cons] at hw'
        simpa using hw'.2) hy
    -- the successor of `z`
    obtain ⟨hd, hhd, hzhd, hInv⟩ : ∃ hd, (zs ++ [y]).head? = some hd ∧
        ((raySystem M st Ω J).edgeWeight z hd).isSome ∧ CandidateInvariant Ω J v hd := by
      cases zs with
      | nil =>
        simp only [List.nil_append] at hw' ⊢
        rw [DifferenceSystem.isWalk_cons_cons] at hw'
        exact ⟨y, rfl, hw'.1, hy⟩
      | cons w ws =>
        rw [List.cons_append, DifferenceSystem.isWalk_cons_cons] at hw'
        exact ⟨w, rfl, hw'.1, (ih w List.mem_cons_self).1⟩
    obtain ⟨hne, a, b, hb, heq⟩ := raySys_edge hzhd
    have hz := ncInv_step hclean hne hb heq hInv
    intro z' hz'
    rcases List.mem_cons.mp hz' with rfl | hz'
    · exact hz
    · exact ih z' hz'
end DeciSigma1.Holes.Tail
