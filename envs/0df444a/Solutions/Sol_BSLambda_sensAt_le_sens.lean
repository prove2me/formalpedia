-- Prove2me | solution 1 for BSLambda.sensAt_le_sens
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:14.381869+00:00
-- url     : https://prove2.me/submissions/8800648f-1589-4ba4-bef8-fed207748e92

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) (x : Input V) : sensAt f x ≤ sens f :=
  Finset.le_sup (Finset.mem_univ x)
end BSLambda
