-- Prove2me | solution 1 for BalanceSpecification.exists_agreeOn_finset_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:48.808372+00:00
-- url     : https://prove2.me/submissions/2e19bcb4-80de-4fe8-99bd-1d27fcff4167

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Theorems.Thm_BalanceSpecification_mem_language_iff_exists_block_zero
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block



set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] {X : ShiftSpace A}
namespace BalanceSpecification
theorem _root_.solution {x : Configuration A}
    (h : ∀ k n, block x k n ∈ language X) (s : Finset ℤ) :
    ∃ y ∈ X.carrier, ∀ i ∈ s, y i = x i := by
  classical
  let M : ℕ := ∑ i ∈ s, i.natAbs
  obtain ⟨y, hy, hblock⟩ := mem_language_iff_exists_block_zero.mp (h (-(M : ℤ)) (2 * M + 1))
  rw [length_block] at hblock
  refine ⟨SymbolicDynamics.FullShift.shift (M : ℤ) y, X.mapsTo (M : ℤ) hy, ?_⟩
  intro i hi
  have habs : i.natAbs ≤ M := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  have hu : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
  have hl : -i ≤ (i.natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -i))
  let j : ℕ := ((M : ℤ) + i).toNat
  have hjcast : (j : ℤ) = (M : ℤ) + i := by
    apply Int.toNat_of_nonneg
    omega
  have hj : j < 2 * M + 1 := by omega
  have he := List.getElem_of_eq hblock
    (show j < (block y 0 (2 * M + 1)).length by simpa only [length_block] using hj)
  simp only [block, List.getElem_ofFn, zero_add] at he
  simpa only [SymbolicDynamics.FullShift.shift_apply, hjcast, neg_add_cancel_left] using he
end BalanceSpecification
