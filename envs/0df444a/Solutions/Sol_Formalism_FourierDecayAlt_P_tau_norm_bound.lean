-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.tau_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:54:19.876274+00:00
-- url     : https://prove2.me/submissions/f28be4bb-717e-46f0-8c3d-cb17836ddf45

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZhatSectionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormEntryBounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormEntryBounds_gN_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormEntryBounds_Hpk_mulVec_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_NormEntryBounds_mul_entry_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_ut_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_entry_le_mx
import Theorems.Thm_Formalism_FourierDecayAlt_P_EntryMinorBounds_inv_entry_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2_tau_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_norm_of_inverse


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 C2x5 HermitianXiVector UnipotentSums EntryMinorBounds
open NormEntryBounds
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.TauBound := by
  intro k r z hz
  have hn0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨Zm, hZm⟩ : ∃ Zm : ℝ, Zm = ∑ p, ‖z p‖ := ⟨_, rfl⟩
  have hZm0 : 0 ≤ Zm := by rw [hZm]; exact Finset.sum_nonneg (fun p _ => norm_nonneg _)
  have hzp : ∀ p, ‖z p‖ ≤ Zm := fun p => by
    rw [hZm]; exact Finset.single_le_sum (fun q _ => norm_nonneg (z q)) (Finset.mem_univ p)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (1 : ℂ) / ((Tz k r z : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 + ‖c‖ * (2 * Zm + 1) := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [norm_nonneg c]
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = (Nat.factorial r : ℝ) := ⟨_, rfl⟩
  have hCm1 : 1 ≤ Cm := by rw [hCm]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero r)
  refine ⟨((2 * r + k + 1 : ℕ) : ℝ) * (((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm)), fun v hv => ?_⟩
  obtain ⟨X, hX⟩ : ∃ X, X = C2.mx v := ⟨_, rfl⟩
  rw [← hX]
  have hX0 : 0 ≤ X := by rw [hX]; exact norm_nonneg _
  have hvX : ∀ a b, ‖v a b‖ ≤ X := fun a b => by rw [hX]; exact entry_le_mx v a b
  have h1X : 1 ≤ 1 + X := by linarith
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Fin r → ℂ, ξ = fun a => v a.castSucc (Fin.last r) := ⟨_, rfl⟩
  obtain ⟨vX, hvXe⟩ : ∃ vX : Matrix (Fin r) (Fin r) ℂ, vX = v.submatrix Fin.castSucc Fin.castSucc := ⟨_, rfl⟩
  have hvXU : vX ∈ C2.UTset r := by
    rw [hvXe]; exact ⟨fun i j h => hv.1 _ _ (Fin.castSucc_lt_castSucc_iff.mpr h), fun i => hv.2 _⟩
  have hτ : C2.tauM k r z v = C2.nEich k r z ξ * C2.mX k r vX := by rw [hξ, hvXe]; rfl
  have hxi : ∀ p, ‖C2.xiV k r ξ p‖ ≤ X := by
    intro p; simp only [C2.xiV]; split_ifs
    · rw [hξ]; exact hvX _ _
    · rw [norm_zero]; exact hX0

  have hnE : ∀ i j, ‖C2.nEich k r z ξ i j‖ ≤ A * (1 + X) ^ 2 := by
    intro i j
    simp only [C2.nEich, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply,
      Pi.star_apply, smul_eq_mul, ← hc]
    have h1 : ‖(1 : B.Mat k r) i j‖ ≤ 1 := by rw [Matrix.one_apply]; split_ifs <;> simp
    have hHz := Hpk_mulVec_le z Zm hzp j
    have hHx := Hpk_mulVec_le (C2.xiV k r ξ) X hxi j
    have hsum : ‖-(C2.xiV k r ξ i * star ((Hpk k r *ᵥ z) j)) + z i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j) +
        1 / 2 * (C2.xiV k r ξ i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j))‖ ≤ (2 * Zm + 1) * (1 + X) ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
      simp only [norm_neg, norm_mul, norm_star]
      have e1 : ‖C2.xiV k r ξ i‖ * ‖(Hpk k r *ᵥ z) j‖ ≤ X * Zm := mul_le_mul (hxi i) hHz (norm_nonneg _) hX0
      have e2 : ‖z i‖ * ‖(Hpk k r *ᵥ C2.xiV k r ξ) j‖ ≤ Zm * X := mul_le_mul (hzp i) hHx (norm_nonneg _) hZm0
      have e3 : ‖(1 / 2 : ℂ)‖ * (‖C2.xiV k r ξ i‖ * ‖(Hpk k r *ᵥ C2.xiV k r ξ) j‖) ≤ 1 * (X * X) := by
        apply mul_le_mul (by norm_num) (mul_le_mul (hxi i) hHx (norm_nonneg _) hX0) (by positivity) (by norm_num)
      nlinarith
    calc _ ≤ ‖(1 : B.Mat k r) i j‖ + ‖c‖ * ‖-(C2.xiV k r ξ i * star ((Hpk k r *ᵥ z) j)) +
            z i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j) +
            1 / 2 * (C2.xiV k r ξ i * star ((Hpk k r *ᵥ C2.xiV k r ξ) j))‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_); rw [norm_mul]
      _ ≤ 1 + ‖c‖ * ((2 * Zm + 1) * (1 + X) ^ 2) := add_le_add h1 (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
      _ ≤ A * (1 + X) ^ 2 := by
          rw [hA]; nlinarith [norm_nonneg c, pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1) h1X 2, sq_nonneg (1 + X)]

  have hvXb : ∀ a b, ‖vX a b‖ ≤ 1 + X := fun a b => by rw [hvXe]; simp only [Matrix.submatrix_apply]; linarith [hvX (Fin.castSucc a) (Fin.castSucc b)]
  have hmE : ∀ i j, ‖C2.mX k r vX i j‖ ≤ Cm * (1 + X) ^ r := by
    have hpow1 : 1 ≤ (1 + X) ^ r := one_le_pow₀ h1X
    intro i j
    simp only [C2.mX]
    split_ifs with h1 h2 h3 h4 h5
    · calc ‖vX _ _‖ ≤ 1 + X := hvXb _ _
        _ ≤ (1 + X) ^ r := by
            calc 1 + X = (1 + X) ^ 1 := (pow_one _).symm
              _ ≤ (1 + X) ^ r := pow_le_pow_right₀ h1X (by omega)
        _ ≤ Cm * (1 + X) ^ r := le_mul_of_one_le_left (by positivity) hCm1
    · rw [norm_zero]; positivity
    · have hdet : vXᴴ.det = 1 := by rw [Matrix.det_conjTranspose, ut_det hvXU, star_one]
      refine (inv_entry_le vXᴴ hdet (1 + X) h1X
        (fun a b => by rw [Matrix.conjTranspose_apply, norm_star]; exact hvXb _ _) _ _).trans ?_
      rw [← hCm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1X (Nat.sub_le r 1)) (by positivity)
    · rw [norm_zero]; positivity
    · rw [norm_one]; nlinarith
    · rw [norm_zero]; positivity
  have hτE : ∀ i j, ‖C2.tauM k r z v i j‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm) * (1 + X) ^ (2 * r + 2) := by
    intro i j
    rw [hτ]
    refine (mul_entry_le _ _ _ _ hnE hmE (by positivity) i j).trans ?_
    have key : ((2 * r + k + 1 : ℕ) : ℝ) * (A * (1 + X) ^ 2 * (Cm * (1 + X) ^ r)) =
        ((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm) * (1 + X) ^ (r + 2) := by ring
    rw [key]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1X (by omega)) (by positivity)
  have hgN : B.gN (C2.tauM k r z v) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * (((2 * r + k + 1 : ℕ) : ℝ) * (A * Cm)) *
      (1 + X) ^ (2 * r + 2) := by
    refine (gN_le _ _ (by positivity) hτE).trans (le_of_eq ?_)
    ring
  have hτG : C2.tauM k r z v ∈ B.GV k r := ((c2_tau_mem k r z hz v hv).1).1
  refine ⟨hgN, ?_⟩
  rw [(norm_of_inverse k r _ hτG).1]
  exact hgN
end Formalism.FourierDecayAlt.P
