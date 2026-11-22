-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.ncInv_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:02:34.811079+00:00
-- url     : https://prove2.me/submissions/ae5184cb-ae0d-4f19-aae9-46746d2b871f

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Theorems.Thm_DeciSigma1_Holes_Tail_edge_step
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Periodic_FollowerEdge_symm
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_nil
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_nil
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_Ray_suffixBeforeOnset_suffix_prefixBeforeOnset
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
omit [Fintype ι]
omit [DecidableEq ι]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (hclean : ∀ u, u ≠ v → NoForbiddenRayOverlap (Ω v) (Ω u) (J v) (J u)) {h x : ι}
    (hhx : h ≠ x) {a b : ℕ} (hb : b ≤ J x) (heq : ∀ t, (Ω h).stream (a + t) = (Ω x).stream (b + t))
    (hx : CandidateInvariant Ω J v x) : CandidateInvariant Ω J v h ∧ h ≠ v := by
  classical
  obtain ⟨hxJ, hXv, hal, hxv⟩ := hx
  obtain ⟨hXx, hal'⟩ := edge_step heq hb hxJ
  have hXvh : (Ω v).suffixBeforeOnset (J v) <:+ (Ω h).prefixBeforeOnset := hXv.trans hXx
  have halv : ∀ t, (Ω v).stream ((Ω v).onset + t) = (Ω h).stream ((Ω h).onset + t) :=
    fun t => ((hal' t).trans (hal t)).symm
  by_cases hhv : h = v
  · subst hhv
    have hlt : ((Ω h).suffixBeforeOnset (J h)).length < ((Ω x).suffixBeforeOnset (J x)).length := by
      rcases hxv with rfl | h' <;> [exact absurd rfl hhx; exact h']
    exfalso
    apply (hclean x (Ne.symm hhx)).2.2
    refine ⟨fun he => by rw [he] at hlt; simp at hlt, hXx, hlt.le⟩
  · have hc := hclean h hhv
    by_cases hA : (Ω h).onset ≤ J h
    · exact absurd ⟨hA, hXvh, halv⟩ hc.2.1
    push Not at hA
    by_cases hlen : ((Ω h).suffixBeforeOnset (J h)).length ≤ ((Ω v).suffixBeforeOnset (J v)).length
    · exact absurd ⟨hA, hXvh, hlen⟩ hc.1
    push Not at hlen
    refine ⟨⟨hA, ?_, fun t => ((halv t).symm), Or.inr hlen⟩, hhv⟩
    exact List.suffix_of_suffix_length_le hXvh
        ((Ω h).suffixBeforeOnset_suffix_prefixBeforeOnset (J h)) hlen.le
end DeciSigma1.Holes.Tail
