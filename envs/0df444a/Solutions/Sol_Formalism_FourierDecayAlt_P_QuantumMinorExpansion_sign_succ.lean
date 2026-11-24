-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorExpansion.sign_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:14:19.224853+00:00
-- url     : https://prove2.me/submissions/24de33e1-c786-46c0-ac97-3da6fdc3598f

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QuantumMinorExpansion
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.Qx6
namespace Formalism.FourierDecayAlt.P.QuantumMinorExpansion
theorem _root_.solution {m : ℕ} (q : Fin (m + 1)) (x : Fin m) :
    ((-1 : ℤ) ^ (x : ℕ)) = (-1) ^ ((q.succAbove x : Fin (m + 1)) : ℕ) * eps (q.succAbove x) q := by
  unfold eps
  by_cases h : x.castSucc < q
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, if_pos (by simpa [Fin.lt_def] using h)]
    simp
  · have h' := not_lt.mp h
    rw [Fin.succAbove_of_le_castSucc _ _ h', if_neg (by simp [Fin.le_def] at h' ⊢; omega)]
    simp [pow_succ]
end Formalism.FourierDecayAlt.P.QuantumMinorExpansion
