-- Prove2me | solution 1 for Formalism.REAL.smooth_on_group_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:16:32.48438+00:00
-- url     : https://prove2.me/submissions/82695a54-3aa1-4cbb-ba53-1a2a3b32b3a4

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
namespace Formalism.REAL
theorem _root_.solution {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) :
    SmoothOnG ε (fun x => starRingEnd ℂ (f x)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun x => starRingEnd ℂ (F x), hU, hgU, ?_, fun g hg hgJ => by
    have := hfF g hg hgJ; simp only at this ⊢; rw [this]⟩
  have := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn hF
  exact this
end Formalism.REAL
