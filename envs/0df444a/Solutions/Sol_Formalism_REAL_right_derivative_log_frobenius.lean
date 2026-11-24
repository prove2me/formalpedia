-- Prove2me | solution 1 for Formalism.REAL.right_derivative_log_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:19:02.948709+00:00
-- url     : https://prove2.me/submissions/7e734d21-ba1e-462f-8529-f9800da48830

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
import Theorems.Thm_Formalism_REAL_mul_exp_zero_smul
import Theorems.Thm_Formalism_REAL_hasDerivAt_frobenius_curve

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
theorem _root_.solution {n : ℕ} (X g : Matrix (Fin n) (Fin n) ℂ) (hpos : 0 < hs g) :
    Rd X (fun x => ((hh x : ℝ) : ℂ)) g =
      (((∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * X) i j)) / hs g : ℝ) : ℂ) := by
  have h0 : hs (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = hs g := by rw [mul_exp_zero_smul]
  have h2 : HasDerivAt (fun t : ℝ => Real.log (hs (g * NormedSpace.exp ((t : ℂ) • X))))
      ((∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * X) i j)) / hs g) 0 := by
    have := (hasDerivAt_frobenius_curve g X).log (by simp only [h0]; exact hpos.ne')
    simpa only [h0] using this
  unfold Rd hh
  exact h2.ofReal_comp.deriv
end Formalism.REAL
