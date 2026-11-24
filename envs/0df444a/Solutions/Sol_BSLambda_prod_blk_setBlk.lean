-- Prove2me | solution 1 for BSLambda.prod_blk_setBlk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:31.975712+00:00
-- url     : https://prove2.me/submissions/fcc3c3c5-d755-4ae5-acf4-f97154db8fbd

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*}
variable [DecidableEq W]
namespace BSLambda
theorem _root_.solution {M : Type*} [Fintype W] [CommMonoid M]
    (u : Input V → M) (x : Input (W × V)) (w : W) (z : Input V) :
    ∏ w' : W, u (blk (setBlk x w z) w') = u z * ∏ w' ∈ Finset.univ.erase w, u (blk x w') := by
  rw [blk_setBlk, ← Finset.mul_prod_erase Finset.univ (fun w' ↦ u (Function.update (blk x) w z w'))
    (Finset.mem_univ w), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun w' hw' ↦
    congrArg u (Function.update_of_ne (Finset.ne_of_mem_erase hw') z (blk x))
end BSLambda
