-- Prove2me | solution 1 for BooleanIsoperimetry.paperColexBlockMove_neighborhood_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:25.31347+00:00
-- url     : https://prove2.me/submissions/32864370-6de2-4ce1-82d7-939f015c2660

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_neighborhood_one_card_le_for_admissible_block
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A A' : Finset (Cube N)} {i j : Fin N}
    (h : IsPaperColexBlockMove A A' i j) : (neighborhood 1 A').card ≤ (neighborhood 1 A).card := by
  have h_adm : IsUVAdmissibleForFamily A {i} {j} := by
    intro x hx
    use i
    constructor
    · apply Finset.mem_singleton_self
    · have hx_eq : x = j := Finset.mem_singleton.mp hx
      subst hx_eq
      rw [Finset.erase_singleton, Finset.erase_singleton]
      unfold familyUp familyUpMap
      ext S
      simp [blockReplace]
  have h_adm_c : IsUVAdmissibleForFamily Aᶜˢ {j} {i} := by
    intro x hx
    use j
    constructor
    · apply Finset.mem_singleton_self
    · have hx_eq : x = i := Finset.mem_singleton.mp hx
      subst hx_eq
      rw [Finset.erase_singleton, Finset.erase_singleton]
      unfold familyUp familyUpMap
      ext S
      simp [blockReplace]
  have hdisj : Disjoint ({i} : Finset (Fin N)) ({j} : Finset (Fin N)) := by
    rw [Finset.disjoint_singleton]
    intro heq; subst heq; exact (lt_self_iff_false i).mp h.2.2
  have heq := h.1
  subst heq
  exact neighborhood_one_card_le_for_admissible_block hdisj h_adm h_adm_c
end BooleanIsoperimetry
