-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorExpansion.skip_two_succAbove_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:39:59.478105+00:00
-- url     : https://prove2.me/submissions/39befa54-83eb-4dfc-9ae8-8c7f6bade0c2

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_skip_succ_double_identity


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
theorem _root_.solution {m : ℕ} (q : Fin (m + 2)) (i' : Fin (m + 1)) :
    (skip2 (min (q.succAbove i') q) (max (q.succAbove i') q) : Fin m → Fin (m + 2)) =
      q.succAbove ∘ i'.succAbove := by
  funext j
  by_cases h : i'.castSucc < q
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, min_eq_left h.le, max_eq_right h.le]
    apply Fin.ext
    simp only [skip2, Function.comp, Fin.succAbove, Fin.lt_def, Fin.val_castSucc] at h ⊢
    split_ifs <;> simp at * <;> omega
  · have h' := not_lt.mp h
    have h2 : q ≤ q.succAbove i' := by
      rw [Fin.succAbove_of_le_castSucc _ _ h']
      exact h'.trans (Fin.castSucc_lt_succ).le
    rw [min_eq_right h2, max_eq_left h2]
    exact skip_succ_double_identity m q i' j (by simpa [Fin.le_def] using h')
end Formalism.FourierDecayAlt.P.QuantumMinorExpansion
