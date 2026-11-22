-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Level.next_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:42.315794+00:00
-- url     : https://prove2.me/submissions/147149d6-9785-472f-aa21-a59e530df5ad

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_infix_of_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_of_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_occ_le_length
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_mem_markerEndCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_lastInteriorCut_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_active
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_active_subset
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_suffix
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Fresh.Level
variable [DecidableEq α] (L : Level α k)
variable {L}
namespace DeciSigma1.Holes.Fresh.Level
theorem _root_.solution (hA : L.FactorAntichain) {W : Fin k → List α} (hS : L.MarkersAreSuffixes W) :
    (L.next W).FactorAntichain := by
  refine ⟨fun l hl => ?_, fun g hg m hm h => ?_⟩
  · obtain ⟨_, -, -, -, -, -, hcat⟩ := next_spec hl
    obtain ⟨-, hex⟩ := next_active.mp hl
    obtain ⟨-, hlt, -⟩ := lastInteriorCut_spec hex
    rw [hcat]
    intro hnil
    have := congrArg List.length hnil
    simp at this
    omega
  · obtain ⟨g', hg', -, -, hlg, -, hcatg⟩ := next_spec hg
    obtain ⟨-, hexg⟩ := next_active.mp hg
    obtain ⟨-, hltg, -⟩ := lastInteriorCut_spec hexg
    obtain ⟨m', hm', -, -, hlm, hmkm, hcatm⟩ := next_spec hm
    obtain ⟨-, hexm⟩ := next_active.mp hm
    obtain ⟨-, hltm, hmaxm⟩ := lastInteriorCut_spec hexm
    obtain ⟨s, r, hsr⟩ := h
    have hO : (L.next W).marker g <+:
        (W m).drop (L.lastInteriorCut (W m) - (L.marker m').length + s.length) := by
      rw [← List.drop_drop, ← hmkm, ← hsr, List.append_assoc, List.drop_left]
      exact List.prefix_append _ _
    have hτgO : L.marker g' <+:
        (W m).drop (L.lastInteriorCut (W m) - (L.marker m').length + s.length) := by
      refine List.IsPrefix.trans ?_ hO
      rw [hcatg]; exact List.prefix_append _ _
    have hτm : L.marker m' <+: (W m).drop (L.lastInteriorCut (W m) - (L.marker m').length) := by
      rw [← hmkm, hcatm]; exact List.prefix_append _ _
    have hlenσg : ((L.next W).marker g).length =
        (L.marker g').length + ((W g).length - L.lastInteriorCut (W g)) := by
      rw [hcatg]; simp
    have hσgne : (L.next W).marker g ≠ [] := by
      intro hnil; have := congrArg List.length hnil; simp only [List.length_nil] at this; omega
    have hOle := occ_le_length hO hσgne
    have hβends : L.lastInteriorCut (W m) - (L.marker m').length + s.length + (L.marker g').length ∈
        L.markerEndCuts (W m) :=
      mem_markerEndCuts.mpr ⟨by omega, g', hg', suffix_take_of_occ hτgO⟩
    have hβle := hmaxm _ hβends (by omega)
    have hinf : L.marker g' <:+: L.marker m' := infix_of_occ hτm hτgO (by omega) (by omega)
    have heqτ := hA.2 g' hg' m' hm' hinf
    have hlenτ : (L.marker g').length = (L.marker m').length := by rw [heqτ]
    have hs0 : s.length = 0 := by omega
    have hsuf : L.marker g <:+ (L.next W).marker g := (next_suffix hA hS hg).1
    have hend : L.lastInteriorCut (W m) - (L.marker m').length + s.length +
        ((L.next W).marker g).length ∈
        L.markerEndCuts (W m) :=
      mem_markerEndCuts.mpr ⟨hOle, g, next_active_subset W hg, hsuf.trans (suffix_take_of_occ hO)⟩
    have hendeq : L.lastInteriorCut (W m) - (L.marker m').length + s.length +
        ((L.next W).marker g).length = (W m).length := by
      by_contra hne
      have := hmaxm _ hend (by omega)
      omega
    have hlenσm : ((L.next W).marker m).length = (W m).length -
        (L.lastInteriorCut (W m) - (L.marker m').length) := by
      rw [hmkm, List.length_drop]
    exact List.IsInfix.eq_of_length ⟨s, r, hsr⟩ (by omega)
end DeciSigma1.Holes.Fresh.Level
