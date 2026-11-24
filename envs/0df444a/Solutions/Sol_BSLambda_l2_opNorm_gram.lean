-- Prove2me | solution 1 for BSLambda.l2_opNorm_gram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:10:14.391366+00:00
-- url     : https://prove2.me/submissions/5f83cec5-cb2e-4a98-9f6b-2bbce5b99f2c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Theorems.Thm_Matrix_l2_opNorm_transpose


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) : ‖gram f‖ = ‖biadj f‖ * ‖biadj f‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self ((biadj f)ᵀ)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at h
  rw [gram, h, Matrix.l2_opNorm_transpose]
end BSLambda
