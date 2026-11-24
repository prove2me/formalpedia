-- Prove2me | solution 1 for BSLambda.iterFun_zeroInput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:54:40.702102+00:00
-- url     : https://prove2.me/submissions/4ffd5fee-3d3e-4c56-9c7d-3650183348f5

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u
variable {V ι : Type*} [DecidableEq V] {f : Input V → Bool} {blk : ι → Finset V}
omit [DecidableEq V]
namespace BSLambda
theorem _root_.solution (hzero : f (zeroInput V) = false) :
    ∀ m, iterFun f m (zeroInput (IterCoord V m)) = false
  | 0 => rfl
  | m + 1 => by
      have h : (fun w ↦ iterFun f m fun v ↦ zeroInput (IterCoord V (m + 1)) (w, v))
          = zeroInput V := funext fun _ ↦ solution hzero m
      exact (congrArg f h).trans hzero
end BSLambda
