-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux4.wMat_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:51:34.92324+00:00
-- url     : https://prove2.me/submissions/76f9ea42-2c1f-4c6c-b175-b69293d1a3aa

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux4
theorem _root_.solution (d : ℕ) : G.wMat d * G.wMat d = 1 := by
  ext a b
  simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a.rev]
  · by_cases h : a = b
    · subst h
      simp [Fin.rev_rev]
    · have h' : b ≠ a.rev.rev := by rw [Fin.rev_rev]; exact Ne.symm h
      simp [h, h', Ne.symm h]
  · intro c _ hc
    simp [hc]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.Ux4
