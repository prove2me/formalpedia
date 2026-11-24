-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.c2x3_det_mono_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:39:35.663258+00:00
-- url     : https://prove2.me/submissions/5cdaffc5-905f-4cd9-aad7-b6b373e5dcb9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution {m k : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (e f : Fin k → Fin m) (he : Function.Injective e) (hf : Function.Injective f)
    (hs : ∀ j, ∃ i, e i = w (f j)) : ((C2.monoP w d).submatrix e f).det ≠ 0 := by
  apply IsUnit.ne_zero
  apply Matrix.isUnit_det_of_left_inverse
    (B := Matrix.of fun j i => if e i = w (f j) then (d (f j))⁻¹ else 0)
  ext j j'
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.submatrix_apply, C2.monoP]
  obtain ⟨i0, hi0⟩ := hs j
  rw [Finset.sum_eq_single i0]
  · rw [if_pos hi0]
    by_cases hjj : j = j'
    · subst hjj; rw [if_pos hi0, Matrix.one_apply_eq]; field_simp [hd (f j)]
    · rw [if_neg, mul_zero, Matrix.one_apply_ne hjj]
      intro e'; apply hjj; rw [hi0] at e'; exact hf (w.injective e')
  · intro i _ hi
    rw [if_neg, zero_mul]
    intro e'; apply hi; exact he (e'.trans hi0.symm)
  · simp
end Formalism.FourierDecayAlt.P
