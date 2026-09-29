-- Prove2me | solution 1 for BookProof.ChapterH4.compress_transfer
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:31:12.189405+00:00
-- url     : https://prove2.me/submissions/75fa8863-948b-4847-b3ed-1594799d92bf

import Mathlib.Analysis.InnerProductSpace.Adjoint
set_option autoImplicit false
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hVV : V.adjoint.comp V = ContinuousLinearMap.id ℂ F)
    (hinv : ∀ x : F, ∃ y : F, X (V x) = V y) (n : ℕ)
    (v : E) (hv : V (V.adjoint v) = v) :
    (X ^ n) v = V (((V.adjoint.comp (X.comp V)) ^ n) (V.adjoint v)) := by
  have hb (x : F) : X (V x) = V ((V.adjoint.comp (X.comp V)) x) := by
    obtain ⟨y, hy⟩ := hinv x
    have hyy := congrArg (fun Y : F →L[ℂ] F => Y y) hVV
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hyy ⊢
    rw [hy, hyy]
  induction n with
  | zero => simpa using hv.symm
  | succ n ih =>
    simp only [pow_succ', ContinuousLinearMap.mul_apply]
    rw [ih, hb]
#print axioms solution
