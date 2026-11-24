-- Prove2me | solution 1 for BSLambda.sens_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:14.820296+00:00
-- url     : https://prove2.me/submissions/41de8621-934c-4637-a442-0d25f1fd6220

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Cube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) {n : ℕ} (h : ∀ x, sensAt f x ≤ n) : sens f ≤ n :=
  Finset.sup_le fun x _ ↦ h x
end BSLambda
