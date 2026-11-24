-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.sf_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:19:25.073801+00:00
-- url     : https://prove2.me/submissions/277c4416-7b0d-4c94-ab5b-a9f9d73fd1e2

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
theorem _root_.solution {Dc : (Fin r → ℂ) → Set (Mx k r)} {Φ : Fn k r E}
    (h : SmoothFam k r i {x | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} Φ) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    SmoothLev k r i (Dc c) (Φ c) := by
  rintro g₀ ⟨hG, hD⟩
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h (c, g₀) ⟨hc, hD⟩ hG
  exact ⟨{g | ((c, g) : XX k r) ∈ U}, fun g => F (c, g), hU.preimage (continuous_const.prodMk continuous_id),
    hxU, hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun g hg => hg),
    fun g hg hgG => hΦ (c, g) hg hgG⟩
end Formalism.FourierDecayAlt.P.Qx3
