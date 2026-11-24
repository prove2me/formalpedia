-- Prove2me | solution 1 for Formalism.REAL.hasDerivAt_right_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:21:27.90693+00:00
-- url     : https://prove2.me/submissions/f31fb7d3-731f-4424-8b0f-3927e9a43713

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
import Theorems.Thm_Formalism_REAL_hasDerivAt_right_derivative
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
private lemma Jm_mul_Jm_self {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num
private lemma inUJ_exp_real_smul_of_inG {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (u : ℝ) : inUJ ε (NormedSpace.exp ((u : ℂ) • X)) := by
  have hJ := Jm_mul_Jm_self ε
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := by
    unfold inG at hX
    exact eq_neg_of_add_eq_zero_left hX
  have h2 : Xᴴ = -(Jm ε * X * Jm ε) := by
    calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
      _ = -(Jm ε * X * Jm ε) := by rw [h1, Matrix.neg_mul]
  have hYc : ((u : ℂ) • X)ᴴ = Jm ε * (-((u : ℂ) • X)) * Jm ε := by
    rw [Matrix.conjTranspose_smul, h2]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  let U : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨Jm ε, Jm ε, hJ, hJ⟩
  have hU : ((u : ℂ) • X)ᴴ = (U : Matrix (Fin n) (Fin n) ℂ) * (-((u : ℂ) • X)) *
      ((U⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := hYc
  unfold inUJ
  rw [← Matrix.exp_conjTranspose, hU, Matrix.exp_units_conj]
  show Jm ε * NormedSpace.exp (-((u : ℂ) • X)) * Jm ε * Jm ε * NormedSpace.exp ((u : ℂ) • X) = Jm ε
  rw [Matrix.mul_assoc (Jm ε * NormedSpace.exp (-((u : ℂ) • X))) (Jm ε) (Jm ε), hJ, Matrix.mul_one,
    Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((u : ℂ) • X)).neg_left),
    neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]
private lemma inUJ_mul_real_place_taylor {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : inUJ ε a) (hb : inUJ ε b) : inUJ ε (a * b) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul, show bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b by
    simp only [Matrix.mul_assoc], ha, hb]
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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {X g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f) (hX : inG ε X) (hg : inUJ ε g) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X)))
      (Rd X f (g * NormedSpace.exp ((t : ℂ) • X))) t := by
  have hm : inUJ ε (g * NormedSpace.exp ((t : ℂ) • X)) := inUJ_mul_real_place_taylor hg (inUJ_exp_real_smul_of_inG hX t)
  have H := hasDerivAt_right_derivative hf hX hm
  have H2 : HasDerivAt (fun u : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X)))
      (Rd X f (g * NormedSpace.exp ((t : ℂ) • X))) (t - t) := by
    rw [sub_self]
    exact H
  have H3 := H2.comp_sub_const t t
  have hfun : (fun s : ℝ => f (g * NormedSpace.exp ((s : ℂ) • X))) =
      (fun s : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp (((s - t : ℝ) : ℂ) • X))) := by
    funext s
    rw [Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _
      (((Commute.refl X).smul_left (t : ℂ)).smul_right ((s - t : ℝ) : ℂ)), ← add_smul,
      show ((t : ℂ) + ((s - t : ℝ) : ℂ)) = (s : ℂ) by push_cast; ring]
  rw [hfun]
  exact H3
end Formalism.REAL
