-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BorderedDeterminants.sumBorder_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:33:44.023625+00:00
-- url     : https://prove2.me/submissions/d4661bce-7669-455a-af53-49a077dd2b46

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BorderedDeterminants

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BorderedDeterminants
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.BorderedDeterminants
theorem _root_.solution {n : ℕ} (Y : Fin n → Module.End ℂ V) (Ψ : Fin n → Fin n → V) (c : Fin n → ℂ) (i : Fin n)
    (hΨ : ∀ x, Ψ i x = 0) (hc : ∀ i', i' ≠ i → c i' = 0) : ∑ x, Y x (∑ i', c i' • Ψ i' x) = 0 := by
  have h0 : ∀ x, ∑ i', c i' • Ψ i' x = 0 := by
    intro x
    refine Finset.sum_eq_zero (fun i' _ => ?_)
    by_cases h : i' = i
    · subst h; rw [hΨ x, smul_zero]
    · rw [hc i' h, zero_smul]
  simp [h0]
end Formalism.FourierDecayAlt.P.BorderedDeterminants
