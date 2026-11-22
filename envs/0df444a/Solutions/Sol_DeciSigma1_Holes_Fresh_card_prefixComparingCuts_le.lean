-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.card_prefixComparingCuts_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:28.740369+00:00
-- url     : https://prove2.me/submissions/370375dd-d79d-4779-a4b1-bdb9d513ffce

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
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_suffixOccurrenceCuts
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Readers_Table_fresh_iff
public import Theorems.Thm_DeciSigma1_Readers_Table_runFrom_runPrefix_drop
public import Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_add
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
theorem _root_.solution {T : Table α S k} {W : Fin k → List α} {j : Fin k}
    (hj : T.Fresh W j)
    (txt : List α) :
    ((range (W j).length).filter (fun b => (W j).drop b <+: txt)).card ≤ Fintype.card S - 1 := by
  have hfr := fresh_iff.mp hj
  have key : ∀ b d, b ∈ suffixOccurrenceCuts W j txt → d ∈ suffixOccurrenceCuts W j txt → b < d →
      T.runPrefix W j b ≠ T.runPrefix W j d := by
    intro b d hb hd hlt hq
    rw [mem_suffixOccurrenceCuts] at hb hd
    have hpre : (W j).drop d <+: (W j).drop b :=
      List.prefix_of_prefix_length_le hd.2 hb.2 (by simp only [List.length_drop]; omega)
    have hrun : T.runPrefix W j (b + ((W j).length - d)) = T.endState W j := by
      rw [runPrefix_add, show (W j).length - d = ((W j).drop d).length by simp,
        ← List.prefix_iff_eq_take.mp hpre, hq, runFrom_runPrefix_drop]
    exact hfr _ (by omega) hrun
  have hinj : Set.InjOn (T.runPrefix W j) (suffixOccurrenceCuts W j txt) := by
    intro b hb d hd hq
    by_contra hbd
    rcases Nat.lt_or_gt_of_ne hbd with hlt | hlt
    · exact key b d hb hd hlt hq
    · exact key d b hd hb hlt hq.symm
  have hmaps : (suffixOccurrenceCuts W j txt).image (T.runPrefix W j) ⊆
      univ.erase (T.endState W j) := by
    intro q hq
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hq
    exact mem_erase.mpr ⟨hfr b (mem_suffixOccurrenceCuts.mp hb).1, mem_univ _⟩
  calc (suffixOccurrenceCuts W j txt).card =
      ((suffixOccurrenceCuts W j txt).image (T.runPrefix W j)).card :=
        (card_image_of_injOn hinj).symm
    _ ≤ (univ.erase (T.endState W j)).card := card_le_card hmaps
    _ = Fintype.card S - 1 := by rw [card_erase_of_mem (mem_univ _), card_univ]
end DeciSigma1.Holes.Fresh
