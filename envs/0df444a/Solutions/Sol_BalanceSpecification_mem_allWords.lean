-- Prove2me | solution 1 for BalanceSpecification.mem_allWords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:30:53.478627+00:00
-- url     : https://prove2.me/submissions/ce68f733-00c1-4ddd-bce5-78106fe7c615

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Counting

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {w : Word A} {n : ℕ} :
    w ∈ allWords n ↔ w.length = n := by
  classical
  constructor
  · intro h
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp h
    exact List.length_ofFn
  · rintro rfl
    exact Finset.mem_image.mpr ⟨fun i => w[i.val], Finset.mem_univ _, List.ofFn_getElem⟩
end BalanceSpecification
