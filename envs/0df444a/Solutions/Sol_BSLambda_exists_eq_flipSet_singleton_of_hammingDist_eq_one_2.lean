-- Prove2me | solution 2 for BSLambda.exists_eq_flipSet_singleton_of_hammingDist_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:58:17.362863+00:00
-- url     : https://prove2.me/submissions/fbb7d3c1-0c73-49e2-97d1-2cef50b61bb8

module
public import Mathlib.InformationTheory.Hamming
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Theorems.Thm_BSLambda_flipSet_filter_ne

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*}
variable [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution {x y : Input V}
    (h : hammingDist x y = 1) : ∃ v, y = flipSet x {v} := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 h
  exact ⟨v, (hv ▸ flipSet_filter_ne x y).symm⟩
end BSLambda
