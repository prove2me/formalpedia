-- Prove2me | solution 1 for Formalism.REAL.smooth_real_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:16:21.785748+00:00
-- url     : https://prove2.me/submissions/6297fa74-5d92-4b89-a91d-8d5a0bbb6910

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
theorem _root_.solution {h : Matrix (Fin n) (Fin n) ℂ → ℝ} (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hh : SmoothOnG ε (fun x => ((h x : ℝ) : ℂ))) :
    SmoothOnG ε (fun x => ((ψ (h x) : ℝ) : ℂ)) := by
  intro g₀ hg₀
  obtain ⟨U, H, hU, hgU, hH, hhH⟩ := hh g₀ hg₀
  refine ⟨U, fun x => ((ψ (H x).re : ℝ) : ℂ), hU, hgU, ?_, fun g hg hgJ => by
    have := hhH g hg hgJ; simp only at this ⊢; rw [← this, Complex.ofReal_re]⟩
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((hψ.comp Complex.reCLM.contDiff).comp_contDiffOn hH)
end Formalism.REAL
