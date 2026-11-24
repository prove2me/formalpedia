-- Prove2me | solution 1 for Formalism.REAL.complex_parts_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:44:12.868317+00:00
-- url     : https://prove2.me/submissions/999760d3-15f9-457b-9de4-c215aa6027ef

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_lie_algebra_signature_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : inG ε P) (hQ : inG ε Q) :
    cpart1 ε (P + Complex.I • Q) = P ∧ cpart2 ε (P + Complex.I • Q) = Q := by
  have hZ : Jm ε * (P + Complex.I • Q)ᴴ * Jm ε = -P + Complex.I • Q := by
    rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, lie_algebra_signature_conj hP, lie_algebra_signature_conj hQ, Complex.star_def, Complex.conj_I]
    module
  unfold cpart1 cpart2
  rw [hZ]
  constructor
  · module
  · have : P + Complex.I • Q + (-P + Complex.I • Q) = (2 * Complex.I) • Q := by module
    rw [this, smul_smul, one_div, inv_mul_cancel₀ (by simp), one_smul]
end Formalism.REAL
