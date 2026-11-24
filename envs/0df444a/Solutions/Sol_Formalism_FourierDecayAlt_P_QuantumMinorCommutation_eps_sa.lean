-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorCommutation.eps_sa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:12.355933+00:00
-- url     : https://prove2.me/submissions/2609c917-43fa-4672-9f79-8c6be4a2228a

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_sa_val

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
    eps (q.succAbove l) q * (-1) ^ ((q.succAbove l : Fin (m + 1)) : ℕ) = (-1) ^ (l : ℕ) := by
  unfold eps
  rw [sa_val]
  split_ifs
  · simp
  · omega
  · rw [pow_succ]; ring
end Formalism.FourierDecayAlt.P.QuantumMinorCommutation
