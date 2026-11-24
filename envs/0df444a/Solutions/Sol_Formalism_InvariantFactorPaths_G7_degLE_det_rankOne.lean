-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.degLE_det_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:50.084866+00:00
-- url     : https://prove2.me/submissions/21811e92-ce32-4726-8714-ec533ca07770

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_mono
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_det_col
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degLE_det_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (jetPair)
variable {κ R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution {K : Type} [Field K] {l : ℕ} {W : Finset κ} (φ : K →+* MvPolynomial κ R)
    (hφ : ∀ a, degLE W 0 (φ a)) (M' : Matrix (Fin l) (Fin l) (MvPolynomial κ R)) (v : Fin l → K)
    (η : Fin l → MvPolynomial κ R) (hM : ∀ i c, degLE W 0 (M' i c)) (hη : ∀ c, degLE W 1 (η c)) :
    degLE W 1 (Matrix.of fun i c => M' i c + φ (v i) * η c).det := by
  classical
  by_cases hv : ∀ i, v i = 0
  · have : (Matrix.of fun i c => M' i c + φ (v i) * η c) = M' := by
      ext i c
      simp [hv i]
    rw [this]
    have := degLE_det_col M' (fun _ => 0) hM
    exact degLE_mono this (by simp)
  · push Not at hv
    obtain ⟨i0, hi0⟩ := hv
    set N : Matrix (Fin l) (Fin l) (MvPolynomial κ R) :=
      Matrix.of fun i c => M' i c + φ (v i) * η c with hN
    set A : Matrix (Fin l) (Fin l) (MvPolynomial κ R) :=
      Matrix.of fun i c => if i = i0 then N i0 c else M' i c + φ (-(v i / v i0)) * M' i0 c with hA
    have hdet : A.det = N.det := by
      refine Matrix.det_eq_of_forall_row_eq_smul_add_const
        (fun i => if i = i0 then 0 else φ (-(v i / v i0))) i0 (by simp) fun i c => ?_
      by_cases hi : i = i0
      · subst hi
        simp [hA]
      · simp only [hA, hN, Matrix.of_apply, if_neg hi]
        have : φ (v i) = φ (v i / v i0) * φ (v i0) := by
          rw [← map_mul, div_mul_cancel₀ _ hi0]
        rw [this, map_neg]
        ring
    rw [← hdet]
    have := degLE_det_row (W := W) A (fun i => if i = i0 then 1 else 0) fun i c => by
      by_cases hi : i = i0
      · simp only [hA, hN, Matrix.of_apply, if_pos hi]
        refine degLE_add (degLE_mono (hM _ _) (Nat.zero_le _)) ?_
        simpa using degLE_mul (hφ (v i0)) (hη c)
      · simp only [hA, Matrix.of_apply, if_neg hi]
        refine degLE_add (hM _ _) ?_
        simpa using degLE_mul (hφ (-(v i / v i0))) (hM i0 c)
    simpa using this
end Formalism.InvariantFactorPaths.G7
