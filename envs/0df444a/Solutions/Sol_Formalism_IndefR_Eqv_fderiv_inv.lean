-- Prove2me | solution 1 for Formalism.IndefR.Eqv.fderiv_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:15.679781+00:00
-- url     : https://prove2.me/submissions/3a154041-de5a-4dff-b532-80c3ddd1f1b7

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.IndefR.Eqv
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}
    {Φ : E → ContinuousMultilinearMap ℝ (fun _ : Fin n => E) H} (hΦ : Differentiable ℝ Φ) (σ : Equiv.Perm (Fin n))
    (hinv : ∀ y u, Φ y (u ∘ σ) = Φ y u) (x w : E) (u : Fin n → E) :
    fderiv ℝ Φ x w (u ∘ σ) = fderiv ℝ Φ x w u := by
  let A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) H →L[ℝ] H :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) H (u ∘ σ) -
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => E) H u
  have hzero : (fun y => A (Φ y)) = fun _ => 0 := by
    funext y
    simp only [A, ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.apply_apply, hinv, sub_self]
  have h1 : fderiv ℝ (fun y => A (Φ y)) x = A.comp (fderiv ℝ Φ x) :=
    (A.hasFDerivAt.comp x (hΦ x).hasFDerivAt).fderiv
  rw [hzero, fderiv_const_apply] at h1
  have h2 := congrArg (fun T => T w) h1
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply, A,
    ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.apply_apply] at h2
  exact (sub_eq_zero.mp h2.symm)
end Formalism.IndefR.Eqv
