-- Prove2me | solution 1 for Formalism.REAL.continuous_smooth_on_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:47:11.387604+00:00
-- url     : https://prove2.me/submissions/70deebd4-0548-4e56-ab4a-511bfe7679c6

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f) :
    Continuous (fun g : UJ ε => f (toM g)) := by
  have hc : Continuous (toM : UJ ε → Matrix (Fin n) (Fin n) ℂ) := by
    unfold toM
    exact Units.continuous_val.comp continuous_subtype_val
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (toM g) g.2
  have hev : (fun g' : UJ ε => F (toM g')) =ᶠ[𝓝 g] (fun g' => f (toM g')) := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)] with g' hg'
    exact (hfF _ hg' g'.2).symm
  exact ContinuousAt.congr ((hF.continuousOn.continuousAt (hU.mem_nhds hgU)).comp hc.continuousAt) hev
end Formalism.REAL
