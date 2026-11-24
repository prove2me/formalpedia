-- Prove2me | solution 1 for BSLambda.le_lam_of_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:03:53.208606+00:00
-- url     : https://prove2.me/submissions/048674d8-497c-44c0-967d-4875491ca5b0

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Theorems.Thm_Matrix_IsHermitian_le_ciSup_eigenvalues


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) {μ : ℝ} {v : Input V → ℝ} (hv : v ≠ 0)
    (hev : adj f *ᵥ v = μ • v) : μ ≤ lam f :=
  (isHermitian_adj f).le_ciSup_eigenvalues hv hev
end BSLambda
