-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.sf_congr_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:38:05.609671+00:00
-- url     : https://prove2.me/submissions/08c712ce-c2f7-4d54-98ed-a845d98928a6

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply

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
theorem _root_.solution {V : Set (XX k r)} {Φ Ψ : Fn k r E} (hV : IsOpen V) (hUV : U₀ ⊆ V)
    (heq : ∀ x ∈ V, x.2 ∈ Glev k r i → Ψ x.1 x.2 = Φ x.1 x.2) (h : SmoothFam k r i U₀ Φ) :
    SmoothFam k r i U₀ Ψ := by
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x₀ hx₀ hg₀
  exact ⟨U ∩ V, F, hU.inter hV, ⟨hxU, hUV hx₀⟩, hF.mono Set.inter_subset_left,
    fun x hx hxG => (heq x hx.2 hxG).trans (hΦ x hx.1 hxG)⟩
end Formalism.FourierDecayAlt.P.Qx3
