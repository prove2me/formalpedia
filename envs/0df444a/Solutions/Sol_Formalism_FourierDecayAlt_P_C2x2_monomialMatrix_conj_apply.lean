-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.monomialMatrix_conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:51.193115+00:00
-- url     : https://prove2.me/submissions/3f3a303b-e74d-4da9-b8e9-7bcb5301804c

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_monomialMatrix_inv

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
theorem _root_.solution (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0)
    (l : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m) :
    ((C2.monoP w d)⁻¹ * l * C2.monoP w d) a b = (d a)⁻¹ * l (w a) (w b) * d b := by
  rw [monomialMatrix_inv w d hd]
  simp only [Matrix.mul_apply, C2.monoP, Matrix.of_apply]
  rw [Finset.sum_eq_single (w b)]
  · rw [if_pos rfl, Finset.sum_eq_single (w a)]
    · simp
    · intro k _ hk
      rw [if_neg (fun e => hk (by rw [e]; simp)), zero_mul]
    · simp
  · intro k _ hk; rw [if_neg hk, mul_zero]
  · simp
end Formalism.FourierDecayAlt.P.C2x2
