-- Prove2me | solution 1 for BSLambda.sum_setBlk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:48.586427+00:00
-- url     : https://prove2.me/submissions/8cc67c79-03ef-4082-ac7c-95731187dbe6

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (w : W) (F : Input (W × V) → ℝ) :
    ∑ y : {x : Input (W × V) // blk x w = zeroInput V}, ∑ a : Input V, F (setBlk y.1 w a)
      = ∑ x : Input (W × V), F x := by
  rw [← Fintype.sum_prod_type_right (f := fun p : Input V ×
    {x : Input (W × V) // blk x w = zeroInput V} ↦ F (setBlk p.2.1 w p.1))]
  exact Equiv.sum_comp (blockEquiv (V := V) w) F
end BSLambda
