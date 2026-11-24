-- Prove2me | solution 1 for Formalism.REAL.hasDerivAt_frobenius_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:01:32.463591+00:00
-- url     : https://prove2.me/submissions/f7ac0b68-3318-4495-8b77-83f70720ffa4

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
import Theorems.Thm_Formalism_REAL_mul_exp_zero_smul
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
private lemma hasDerivAt_mul_matrix_exp_smul {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g * NormedSpace.exp ((s : ℂ) • X))
      (g * (NormedSpace.exp ((t : ℂ) • X) * X)) t := by
  letI i1 : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI i2 : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI i3 : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI i4 : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedSpace
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h3 : ∀ s : ℝ, ((s : ℂ) • X) = s • X := fun s => by
    ext i j
    simp [Complex.real_smul]
  simp only [h3]
  exact (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).const_mul g
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
theorem _root_.solution {n : ℕ} (g X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => hs (g * NormedSpace.exp ((t : ℂ) • X)))
      (∑ i, ∑ j, 2 * inner ℝ (g i j) ((g * X) i j)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) (g * X) 0 := by
    have h2 := hasDerivAt_mul_matrix_exp_smul g X 0
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul] at h2
    exact h2
  have hentry : ∀ i j, HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) i j) ((g * X) i j) 0 :=
    fun i j => hasDerivAt_pi.1 (hasDerivAt_pi.1 hc i) j
  have hE : ∀ i j, HasDerivAt (fun t : ℝ => ‖(g * NormedSpace.exp ((t : ℂ) • X)) i j‖ ^ 2)
      (2 * inner ℝ (g i j) ((g * X) i j)) 0 := by
    intro i j
    convert (hentry i j).norm_sq using 1
    beta_reduce
    rw [mul_exp_zero_smul]
  have hS := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => HasDerivAt.sum (u := Finset.univ) (fun j _ => hE i j))
  unfold hs
  have hfun : (fun t : ℝ => ∑ i, ∑ j, ‖(g * NormedSpace.exp ((t : ℂ) • X)) i j‖ ^ 2) =
      ∑ i, ∑ j, fun t : ℝ => ‖(g * NormedSpace.exp ((t : ℂ) • X)) i j‖ ^ 2 := by
    funext t
    simp only [Finset.sum_apply]
  rw [hfun]
  exact hS
end Formalism.REAL
