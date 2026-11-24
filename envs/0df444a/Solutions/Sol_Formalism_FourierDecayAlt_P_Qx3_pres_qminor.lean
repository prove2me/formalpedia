-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.pres_qminor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:49:37.265827+00:00
-- url     : https://prove2.me/submissions/8b0f36e7-ef3c-4ad2-a5a8-6c5ad22f63bc

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_csmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_pres_Top
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_pres_foldr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    Pres (E := E) i U₀ (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u) := by
  intro Φ h
  have key : ∀ σ : Equiv.Perm (Fin t), SmoothFam k r i U₀ (fun c g =>
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun j : Fin t =>
        Top (E := E) (EH k r) (u - ((j : ℕ) : ℂ)) ((posL k r i ∘ a) (σ j)) ((posL k r i ∘ b) j)).foldr
          (fun T h => T h) (Φ c) g)) := by
    intro σ
    refine sf_csmul _ (pres_foldr _ ?_ Φ h)
    intro T hT
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact pres_Top _ _ _
  have := sf_sum Finset.univ (fun σ _ => key σ)
  convert this using 3
  simp [qminorOp, Finset.sum_apply]
end Formalism.FourierDecayAlt.P.Qx3
