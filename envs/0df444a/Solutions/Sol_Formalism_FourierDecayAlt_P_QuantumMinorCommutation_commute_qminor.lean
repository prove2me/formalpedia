-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QuantumMinorCommutation.commute_qminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:34:58.254521+00:00
-- url     : https://prove2.me/submissions/f8a1d42f-7348-48c8-a8ad-496cbb78cc56

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Theorems.Thm_Formalism_FourierDecayAlt_P_QuantumMinorCommutation_commute_Tm

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
theorem _root_.solution {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (x : A)
    (h : ∀ s s', Commute x (E (a s) (b s'))) : Commute x (qminor E a b u) := by
  unfold qminor
  refine Commute.sum_right _ _ _ (fun σ _ => ?_)
  refine Commute.mul_right (Int.commute_cast x _) ?_
  refine Commute.list_prod_right _ _ (fun y hy => ?_)
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hy
  exact commute_Tm E _ _ _ x (h _ _)
end Formalism.FourierDecayAlt.P.QuantumMinorCommutation
