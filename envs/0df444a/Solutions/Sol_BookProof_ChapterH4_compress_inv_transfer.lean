-- Prove2me | solution 1 for BookProof.ChapterH4.compress_inv_transfer
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:31:11.446639+00:00
-- url     : https://prove2.me/submissions/53eb1303-e26a-4ca2-baae-2666a0ff1668

import Mathlib.Analysis.InnerProductSpace.Adjoint
set_option autoImplicit false
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem solution (V : F →L[ℂ] E)
    (qX qXinv : E →L[ℂ] E) (qB qBinv : F →L[ℂ] F)
    (hintertwine : qX.comp V = V.comp qB)
    (hqXl : qXinv.comp qX = ContinuousLinearMap.id ℂ E)
    (hqBr : qB.comp qBinv = ContinuousLinearMap.id ℂ F) :
    qXinv.comp V = V.comp qBinv := by
  ext v
  have hB := congrArg (fun Y : F →L[ℂ] F => Y v) hqBr
  have hi := congrArg (fun Y : F →L[ℂ] E => Y (qBinv v)) hintertwine
  have hX := congrArg (fun Y : E →L[ℂ] E => Y (V (qBinv v))) hqXl
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hB hi hX ⊢
  calc
    qXinv (V v) = qXinv (V (qB (qBinv v))) := congrArg (fun w => qXinv (V w)) hB.symm
    _ = qXinv (qX (V (qBinv v))) := congrArg qXinv hi.symm
    _ = V (qBinv v) := hX
#print axioms solution
