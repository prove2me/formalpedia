-- Prove2me | solution 1 for BSLambda.biadj_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:02:03.797777+00:00
-- url     : https://prove2.me/submissions/ca01caa6-db30-4793-8d61-74ab959d51ea

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
omit [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) (x : Ones f) (z : Zeros f) :
    biadj f x z = if hammingDist x.1 z.1 = 1 then (1 : ℝ) else 0 := rfl
end BSLambda
