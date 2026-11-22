-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Level.next_markerEndCuts_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:42.871888+00:00
-- url     : https://prove2.me/submissions/37f76ee9-402e-4738-891a-6586546c06a0

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_suffix_take_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_infix_of_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_mem_markerEndCuts
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_lastInteriorCut_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_next_active
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
theorem _root_.solution (hA : L.FactorAntichain) {W : Fin k → List α}
    (hS : L.MarkersAreSuffixes W)
    {l : Fin k}
    (hl : l ∈ (L.next W).active) :
    ∃ m ∈ L.active, L.marker m <+: (L.next W).marker l ∧
      (L.marker m).length < ((L.next W).marker l).length ∧
      L.markerEndCuts ((L.next W).marker l) =
          {(L.marker m).length, ((L.next W).marker l).length} := by
  obtain ⟨m, hm, -, -, hlm, hmk, hcat⟩ := next_spec hl
  obtain ⟨hlact, hex⟩ := next_active.mp hl
  obtain ⟨-, hlt, hmax⟩ := lastInteriorCut_spec hex
  have hpre : L.marker m <+: (L.next W).marker l := by rw [hcat]; exact List.prefix_append _ _
  have hτocc : L.marker m <+: (W l).drop (L.lastInteriorCut (W l) - (L.marker m).length) := by
    rw [← hmk]; exact hpre
  have hσlen : ((L.next W).marker l).length =
      (W l).length - (L.lastInteriorCut (W l) - (L.marker m).length) := by
    rw [hmk, List.length_drop]
  have hτlt : (L.marker m).length < ((L.next W).marker l).length := by
    rw [hcat, List.length_append, List.length_drop]; omega
  refine ⟨m, hm, hpre, hτlt, ?_⟩
  ext p
  simp only [mem_insert, mem_singleton, mem_markerEndCuts]
  constructor
  · rintro ⟨hp, h, hh, hsuf⟩
    have htake : (W l).take (L.lastInteriorCut (W l) - (L.marker m).length + p) =
        (W l).take (L.lastInteriorCut (W l) - (L.marker m).length) ++
            ((L.next W).marker l).take p := by
      rw [List.take_add, hmk]
    have hsufx : L.marker h <:+ (W l).take (L.lastInteriorCut (W l) - (L.marker m).length + p) := by
      rw [htake]; exact hsuf.trans (List.suffix_append _ _)
    have hpe : L.lastInteriorCut (W l) - (L.marker m).length + p ∈ L.markerEndCuts (W l) :=
      mem_markerEndCuts.mpr ⟨by omega, h, hh, hsufx⟩
    rcases Nat.lt_or_ge (L.lastInteriorCut (W l) - (L.marker m).length + p)
        (W l).length with hlt' | hge
    · have hle := hmax _ hpe hlt'
      rcases lt_or_eq_of_le hle with hlt2 | heq
      · exfalso
        have hptake : p ≤ ((L.next W).marker l).length := hp
        obtain ⟨hhl, hocc⟩ := (suffix_take_iff hptake).mp hsuf
        have hocc' : L.marker h <+: (W l).drop
            (L.lastInteriorCut (W l) - (L.marker m).length + (p - (L.marker h).length)) := by
          rw [← List.drop_drop, ← hmk]; exact hocc
        have hinf : L.marker h <:+: L.marker m := infix_of_occ hτocc hocc' (by omega) (by omega)
        have heq := hA.2 h hh m hm hinf
        have : (L.marker h).length = (L.marker m).length := by rw [heq]
        omega
      · left; omega
    · right; omega
  · rintro (rfl | rfl)
    · refine ⟨hpre.length_le, m, hm, ?_⟩
      rw [← List.prefix_iff_eq_take.mp hpre]
    · refine ⟨le_rfl, l, hlact, ?_⟩
      rw [List.take_length]; exact (next_suffix hA hS hl).1
end DeciSigma1.Holes.Fresh.Level
