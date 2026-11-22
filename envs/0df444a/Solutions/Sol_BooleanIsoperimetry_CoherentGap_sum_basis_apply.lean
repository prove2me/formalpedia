-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.sum_basis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:47.809378+00:00
-- url     : https://prove2.me/submissions/4579ea48-99e8-4881-8f82-13aba665d251

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_relation_finset_sum_apply
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {sourceDimension targetDimension : ℕ}
    (embedding : Fin sourceDimension → Fin targetDimension)
    (hinjective : Function.Injective embedding)
    (coordinate : Fin targetDimension) :
    (∑ index, basis (embedding index)) coordinate =
      if coordinate ∈ Finset.univ.image embedding then 1 else 0 := by
  classical
  rw [relation_finset_sum_apply]
  calc
    (∑ index, basis (embedding index) coordinate) =
        ∑ imageCoordinate ∈ Finset.univ.image embedding,
          basis imageCoordinate coordinate := by
      symm
      simpa using Finset.sum_image hinjective.injOn
    _ = if coordinate ∈ Finset.univ.image embedding then 1 else 0 := by
      simp [basis]
end BooleanIsoperimetry.CoherentGap
