-- Prove2me | solution 1 for Finset.affineDim_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:27.92809+00:00
-- url     : https://prove2.me/submissions/75252451-13f3-43c5-96fc-bedfac221905

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
theorem _root_.solution (S : Finset (Fin D → ℝ)) : S.affineDim ≤ D :=
  (Submodule.finrank_le _).trans_eq (Module.finrank_fin_fun ℝ)
end Finset
