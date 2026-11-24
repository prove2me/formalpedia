-- Prove2me | solution 1 for BSLambda.biadj_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:23.429385+00:00
-- url     : https://prove2.me/submissions/4b335007-8506-4a29-8c98-c8d150d61002

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Theorems.Thm_BSLambda_biadj_apply

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) (x : Ones f) (z : Zeros f) : 0 ≤ biadj f x z := by
  rw [biadj_apply]
  positivity
end BSLambda
