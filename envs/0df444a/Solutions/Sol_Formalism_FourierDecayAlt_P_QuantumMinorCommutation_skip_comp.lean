-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorCommutation.skip_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:35:11.443227+00:00
-- url     : https://prove2.me/submissions/448814e0-942a-4ff4-a1b7-b7d39ae8fed2

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_sa_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp


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
theorem _root_.solution {m : ℕ} (q : Fin (m + 2)) (l : Fin (m + 1)) :
    (q.succAbove ∘ l.succAbove : Fin m → Fin (m + 2)) = skip2 (min (q.succAbove l) q) (max (q.succAbove l) q) := by
  funext k
  apply Fin.ext
  simp only [Function.comp, skip2, Fin.coe_min, Fin.coe_max, sa_val]
  split_ifs <;> simp only [] <;> omega
end Formalism.FourierDecayAlt.P.QuantumMinorCommutation
