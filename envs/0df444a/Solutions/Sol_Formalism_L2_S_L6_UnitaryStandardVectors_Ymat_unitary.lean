-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.Ymat_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:17:48.859908+00:00
-- url     : https://prove2.me/submissions/cb1cb332-2222-4122-a465-e27b4540333b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RankUpdateMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.L6 Formalism.L2.S.L6.UnitaryStandardVectors
variable {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.L2.S.L6.UnitaryStandardVectors
theorem _root_.solution (J : Matrix n n ℂ) (hJ : Jᴴ = J) (W : Matrix n ι ℂ) (M : Matrix ι ι ℂ)
    (hΓ : IsUnit (Wᴴ * J * W).det) (hM : (1 + M)ᴴ * (Wᴴ * J * W) * (1 + M) = Wᴴ * J * W) :
    (Ymat J W M)ᴴ * J * Ymat J W M = J := by
  have hGh : (Wᴴ * J * W)ᴴ = Wᴴ * J * W := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ,
      Matrix.mul_assoc]
  have hGi1 : (Wᴴ * J * W)⁻¹ * (Wᴴ * J * W) = 1 := Matrix.nonsing_inv_mul _ hΓ
  have hGi2 : (Wᴴ * J * W) * (Wᴴ * J * W)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hΓ
  have hGih : ((Wᴴ * J * W)⁻¹)ᴴ = (Wᴴ * J * W)⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hGh]
  unfold Ymat
  set G := Wᴴ * J * W with hG
  set Gi := G⁻¹ with hGi

  have hK : G * M + Mᴴ * G + Mᴴ * G * M = 0 := by
    have h' := hM
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one] at h'
    have e : (1 + Mᴴ) * G * (1 + M) = G + (G * M + Mᴴ * G + Mᴴ * G * M) := by noncomm_ring
    rw [e] at h'
    exact add_eq_left.1 h'
  have hbr : M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi = 0 := by
    calc M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi
        = Gi * G * M * Gi + Gi * Mᴴ * (G * Gi) + Gi * Mᴴ * G * M * Gi := by
          rw [hGi1, hGi2]
          noncomm_ring
      _ = Gi * (G * M + Mᴴ * G + Mᴴ * G * M) * Gi := by noncomm_ring
      _ = 0 := by rw [hK]; noncomm_ring
  have key : J * W * (M * Gi + Gi * Mᴴ + Gi * Mᴴ * G * M * Gi) * Wᴴ * J = 0 := by
    rw [hbr]
    simp
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hJ, hGih]
  refine Eq.trans ?_ (add_zero J)
  rw [← key]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, hG]
  abel
end Formalism.L2.S.L6.UnitaryStandardVectors
