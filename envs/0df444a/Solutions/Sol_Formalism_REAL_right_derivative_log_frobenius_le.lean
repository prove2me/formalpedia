-- Prove2me | solution 1 for Formalism.REAL.right_derivative_log_frobenius_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:37:43.953404+00:00
-- url     : https://prove2.me/submissions/cfff0548-7486-4bb3-8a76-28ec2bd5ac68

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
import Theorems.Thm_Formalism_REAL_frobenius_nonneg
import Theorems.Thm_Formalism_REAL_frobenius_cauchy_schwarz
import Theorems.Thm_Formalism_REAL_frobenius_mul_le
import Theorems.Thm_Formalism_REAL_frobenius_pos_of_indefinite_unitary
import Theorems.Thm_Formalism_REAL_right_derivative_log_frobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.REAL
section F4ALinfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end F4ALinfty
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
private lemma bound_of_hs_pos {n : ℕ} (X g : Matrix (Fin n) (Fin n) ℂ) (hpos : 0 < hs g) :
    |(∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * X) i j)) / hs g| ≤ 2 * Real.sqrt (hs X) := by
  have h1 : |∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * X) i j)| ≤
      2 * ∑ i, ∑ j, ‖g i j‖ * ‖(g * X) i j‖ := by
    calc |∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * X) i j)|
          ≤ ∑ i, ∑ j, |2 * inner ℝ (g i j) ((g * X) i j)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            gcongr with i _
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, 2 * (‖g i j‖ * ‖(g * X) i j‖) := by
            gcongr with i _ j _
            rw [abs_mul, abs_two]
            gcongr
            exact abs_real_inner_le_norm _ _
      _ = 2 * ∑ i, ∑ j, ‖g i j‖ * ‖(g * X) i j‖ := by simp only [Finset.mul_sum]
  have hT0 : 0 ≤ ∑ i, ∑ j, ‖g i j‖ * ‖(g * X) i j‖ := by positivity
  have hX0 := frobenius_nonneg X
  have hB0 : 0 ≤ hs g * Real.sqrt (hs X) := by positivity
  have hsq : (∑ i, ∑ j, ‖g i j‖ * ‖(g * X) i j‖) ^ 2 ≤ (hs g * Real.sqrt (hs X)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hX0]
    calc (∑ i, ∑ j, ‖g i j‖ * ‖(g * X) i j‖) ^ 2 ≤ hs g * hs (g * X) := frobenius_cauchy_schwarz g (g * X)
      _ ≤ hs g * (hs g * hs X) := by gcongr; exact frobenius_mul_le g X
      _ = hs g ^ 2 * hs X := by ring
  have hT : ∑ i, ∑ j, ‖g i j‖ * ‖(g * X) i j‖ ≤ hs g * Real.sqrt (hs X) := by nlinarith
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  nlinarith
end Formalism.REAL
end
end

set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (X g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    ‖Rd X (fun x => ((hh x : ℝ) : ℂ)) g‖ ≤ 2 * Real.sqrt (hs X) := by
  rcases isEmpty_or_nonempty (Fin n) with hE | hN
  · have : ∀ x : Matrix (Fin n) (Fin n) ℂ, hs x = 0 := fun x => by simp [hs]
    simp only [Rd, hh, this, Real.log_zero, Complex.ofReal_zero, deriv_const, norm_zero]
    positivity
  · have hpos := frobenius_pos_of_indefinite_unitary hg
    rw [right_derivative_log_frobenius X g hpos, Complex.norm_real, Real.norm_eq_abs]
    exact bound_of_hs_pos X g hpos
end Formalism.REAL
