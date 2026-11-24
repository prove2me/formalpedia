-- Prove2me | solution 1 for Formalism.REAL.right_derivative_zero_outside_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:01:40.295671+00:00
-- url     : https://prove2.me/submissions/c3fd7165-2ec7-4a36-88aa-aa54f0a62783

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport
import Theorems.Thm_Formalism_REAL_contDiff_frobenius
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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {φ : Matrix (Fin n) (Fin n) ℂ → ℂ}
    {X h : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hX : inG ε X) (hh : inUJ ε h)
    (hsupp : ∀ g, inUJ ε g → R < hs g → φ g = 0) (hR : R < hs h) : Rd X φ h = 0 := by
  have hcont : ContinuousAt (fun u : ℝ => h * NormedSpace.exp ((u : ℂ) • X)) 0 :=
    (hasDerivAt_mul_matrix_exp_smul h X 0).continuousAt
  have hc2 : ContinuousAt (fun u : ℝ => hs (h * NormedSpace.exp ((u : ℂ) • X))) 0 :=
    contDiff_frobenius.continuous.continuousAt.comp hcont
  have h0 : R < hs (h * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [mul_exp_zero_smul]
    exact hR
  have hR' : ∀ᶠ u : ℝ in 𝓝 (0 : ℝ), R < hs (h * NormedSpace.exp ((u : ℂ) • X)) :=
    hc2.eventually (lt_mem_nhds h0)
  have hev : (fun u : ℝ => φ (h * NormedSpace.exp ((u : ℂ) • X))) =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
    filter_upwards [hR'] with u hu
    exact hsupp _ (inUJ_mul_real_place_taylor hh (inUJ_exp_real_smul_of_inG hX u)) hu
  unfold Rd
  rw [hev.deriv_eq]
  simp
end Formalism.REAL
