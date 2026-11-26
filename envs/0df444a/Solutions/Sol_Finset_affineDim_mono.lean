-- Prove2me | solution 1 for Finset.affineDim_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:52.16315+00:00
-- url     : https://prove2.me/submissions/e80908a4-28ed-4e9f-a336-1d7b0c61cceb

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDim

set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
variable {D : ℕ}
namespace Finset
theorem _root_.solution {S T : Finset (Fin D → ℝ)}
    (hST : S ⊆ T) : S.affineDim ≤ T.affineDim := by
  unfold affineDim
  apply Submodule.finrank_mono
  apply AffineSubspace.direction_le
  apply affineSpan_mono
  simpa using hST
end Finset
