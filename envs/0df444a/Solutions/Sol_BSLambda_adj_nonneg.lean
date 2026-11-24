-- Prove2me | solution 1 for BSLambda.adj_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:04:14.737999+00:00
-- url     : https://prove2.me/submissions/06837e24-0606-4297-97b7-5f76d436a168

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) (x y : Input V) : 0 ≤ adj f x y := by
  rw [adj_apply]
  positivity
end BSLambda
