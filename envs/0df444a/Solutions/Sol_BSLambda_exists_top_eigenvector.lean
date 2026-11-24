-- Prove2me | solution 1 for BSLambda.exists_top_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:34:48.47158+00:00
-- url     : https://prove2.me/submissions/1f820339-8277-430c-89ed-a539b38786d0

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Theorems.Thm_Matrix_IsHermitian_exists_eigenvector_ciSup_eigenvalues


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) :
    ∃ u : Input V → ℝ, u ≠ 0 ∧ adj f *ᵥ u = lam f • u :=
  (isHermitian_adj f).exists_eigenvector_ciSup_eigenvalues
end BSLambda
