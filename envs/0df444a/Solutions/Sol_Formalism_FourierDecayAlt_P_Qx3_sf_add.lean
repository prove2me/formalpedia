-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.sf_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:34:59.029645+00:00
-- url     : https://prove2.me/submissions/97b4132f-b383-4c7f-bb26-0fa46eac87eb

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
theorem _root_.solution {Φ Ψ : Fn k r E} (h : SmoothFam k r i U₀ Φ) (h' : SmoothFam k r i U₀ Ψ) :
    SmoothFam k r i U₀ (fun c g => Φ c g + Ψ c g) := by
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x₀ hx₀ hg₀
  obtain ⟨U', F', hU', hxU', hF', hΦ'⟩ := h' x₀ hx₀ hg₀
  exact ⟨U ∩ U', fun x => F x + F' x, hU.inter hU', ⟨hxU, hxU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right),
    fun x hx hxG => by
      show Φ x.1 x.2 + Ψ x.1 x.2 = F x + F' x
      rw [hΦ x hx.1 hxG, hΦ' x hx.2 hxG]⟩
end Formalism.FourierDecayAlt.P.Qx3
