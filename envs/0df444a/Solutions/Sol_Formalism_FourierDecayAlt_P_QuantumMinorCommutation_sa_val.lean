-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorCommutation.sa_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:14:17.26174+00:00
-- url     : https://prove2.me/submissions/09f6185d-13f3-4d17-837d-20af29127863

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
namespace Formalism.FourierDecayAlt.P.QuantumMinorCommutation
theorem _root_.solution {m : ℕ} (q : Fin (m + 1)) (l : Fin m) :
    ((q.succAbove l : Fin (m + 1)) : ℕ) = if (l : ℕ) < (q : ℕ) then (l : ℕ) else (l : ℕ) + 1 := by
  unfold Fin.succAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.QuantumMinorCommutation
