-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x2.bt_mul_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:16.391496+00:00
-- url     : https://prove2.me/submissions/1bac1ce2-d4c4-43ae-b46c-614e2839506a

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
theorem _root_.solution {α : Type*} [LinearOrder α] {b : Fin m → α} (hb : Function.Injective b)
    {M N : Matrix (Fin m) (Fin m) ℂ} (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) (i : Fin m) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne (hb.ne hk) with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · simp
end Formalism.FourierDecayAlt.P.C2x2
