-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorExpansion.signs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:58:16.761096+00:00
-- url     : https://prove2.me/submissions/a91b19e6-3501-43a2-92ae-9d9ed97f239d

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorExpansion_sign_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorExpansion_eps_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorExpansion_eps_swap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hsq


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
variable {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 2) → Fin (m + 2) → A)
namespace Formalism.FourierDecayAlt.P.QuantumMinorExpansion
theorem _root_.solution (q : Fin (m + 2)) (i' q' : Fin (m + 1)) (hq' : (q.succAbove i').succAbove q' = q) :
    (-eps (q.succAbove i') q) * (-1) ^ (q' : ℕ) = (-1) ^ (q : ℕ) ∧
      (-eps (q.succAbove i') q) * (-1) ^ (i' : ℕ) = -(-1) ^ ((q.succAbove i' : Fin (m + 2)) : ℕ) := by
  have hne : q.succAbove i' ≠ q := Fin.succAbove_ne _ _
  have hsq := eps_sq (q.succAbove i') q
  constructor
  · have h := sign_succ (q.succAbove i') q'
    rw [hq', eps_swap hne] at h
    rw [h]
    linear_combination ((-1) ^ (q : ℕ)) * hsq
  · rw [sign_succ q i']
    linear_combination (-(-1) ^ ((q.succAbove i' : Fin (m + 2)) : ℕ)) * hsq
end Formalism.FourierDecayAlt.P.QuantumMinorExpansion
