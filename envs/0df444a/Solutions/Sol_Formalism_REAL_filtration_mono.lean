-- Prove2me | solution 1 for Formalism.REAL.filtration_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:07.842074+00:00
-- url     : https://prove2.me/submissions/4f0afa48-1497-4791-b4b6-08acd25fc667

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
variable (ε)
variable {ε}
variable {W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)}
namespace Formalism.REAL
theorem _root_.solution {k k' : ℕ} (h : k ≤ k') : wordFiltration ε W k ≤ wordFiltration ε W k' :=
  Submodule.span_mono fun _ ⟨w, m, hm, hw, hx⟩ => ⟨w, m, hm, hw.trans h, hx⟩
end Formalism.REAL
