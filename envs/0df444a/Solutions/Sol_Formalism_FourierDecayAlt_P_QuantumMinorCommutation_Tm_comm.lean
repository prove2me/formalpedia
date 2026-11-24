-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorCommutation.Tm_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:17:46.121414+00:00
-- url     : https://prove2.me/submissions/2563d44d-da42-4524-a39f-c90d0734da60

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QuantumMinorCommutation
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
namespace Formalism.FourierDecayAlt.P.QuantumMinorCommutation
theorem _root_.solution (v : ℂ) (a b : Fin n) (x : A) :
    Tm E v a b * x - x * Tm E v a b = E a b * x - x * E a b := by
  unfold Tm
  have h : (if a = b then algebraMap ℂ A v else 0) * x = x * (if a = b then algebraMap ℂ A v else 0) := by
    split_ifs
    · exact Algebra.commutes v x
    · simp
  rw [add_mul, mul_add, h]
  abel
end Formalism.FourierDecayAlt.P.QuantumMinorCommutation
