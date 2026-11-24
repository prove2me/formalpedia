-- Prove2me | solution 1 for BSLambda.gram_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:24.064726+00:00
-- url     : https://prove2.me/submissions/3e86439b-2f7c-431a-8e2c-57b84775c5c9

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) : (gram f).IsHermitian := by
  rw [gram, ← Matrix.conjTranspose_eq_transpose_of_trivial]
  exact Matrix.isHermitian_mul_conjTranspose_self _
end BSLambda
