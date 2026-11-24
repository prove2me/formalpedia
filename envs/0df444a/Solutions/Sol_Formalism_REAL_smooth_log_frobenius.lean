-- Prove2me | solution 1 for Formalism.REAL.smooth_log_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:17:27.567137+00:00
-- url     : https://prove2.me/submissions/e329be43-51d7-4a60-906c-dec713475e37

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
import Theorems.Thm_Formalism_REAL_contDiff_frobenius
import Theorems.Thm_Formalism_REAL_frobenius_pos_of_indefinite_unitary

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
theorem _root_.solution (n : ℕ) (ε : Fin n → Bool) : SmoothOnG ε (fun x => ((hh x : ℝ) : ℂ)) := by
  intro g₀ hg₀
  rcases isEmpty_or_nonempty (Fin n) with hE | hN
  · refine ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => ?_⟩
    simp [hh, hs]
  · refine ⟨{g | 0 < hs g}, fun x => ((hh x : ℝ) : ℂ),
      isOpen_lt continuous_const contDiff_frobenius.continuous, frobenius_pos_of_indefinite_unitary hg₀, ?_, fun g _ _ => rfl⟩
    have h1 : ContDiffOn ℝ ∞ (fun x => hh x) {g : Matrix (Fin n) (Fin n) ℂ | 0 < hs g} := by
      unfold hh
      exact contDiff_frobenius.contDiffOn.log (fun x hx => ne_of_gt hx)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1
end Formalism.REAL
