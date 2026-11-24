-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.monomialMatrix_inv_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:39:29.266492+00:00
-- url     : https://prove2.me/submissions/a2f6b1ad-9222-4ad7-8055-02f2b6726537

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates

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
open Formalism.FourierDecayAlt.P.C2x2
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x2
theorem _root_.solution (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    C2.monoP w.symm (fun i => (d (w.symm i))⁻¹) * C2.monoP w d = 1 := by
  ext i j
  simp only [C2.monoP, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (w j)]
  · by_cases hij : i = j
    · subst hij; simp [hd i]
    · rw [if_neg (by simpa using hij), zero_mul, Matrix.one_apply_ne hij]
  · intro k _ hk; rw [if_neg hk, mul_zero]
  · simp
end Formalism.FourierDecayAlt.P.C2x2
