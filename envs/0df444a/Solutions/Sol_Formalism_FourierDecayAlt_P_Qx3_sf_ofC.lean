-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.sf_ofC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:21:16.18868+00:00
-- url     : https://prove2.me/submissions/a8c73daf-88fa-4df3-9939-703e3493ab9a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_isOpen_OmXX

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
theorem _root_.solution {ρ : (Fin r → ℂ) → ℂ} (hρ : ContDiffOn ℝ ∞ ρ (OmX r)) (hU₀ : U₀ ⊆ {x | x.1 ∈ OmX r}) :
    SmoothFam k r i U₀ (fun c _ => ρ c) :=
  fun _ hx₀ _ => ⟨{x | x.1 ∈ OmX r}, fun x => ρ x.1, isOpen_OmXX, hU₀ hx₀,
    hρ.comp contDiff_fst.contDiffOn (fun _ hx => hx), fun _ _ _ => rfl⟩
end Formalism.FourierDecayAlt.P.Qx3
