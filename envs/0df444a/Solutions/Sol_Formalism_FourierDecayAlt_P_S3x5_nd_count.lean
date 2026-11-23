-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.nd_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:25.393967+00:00
-- url     : https://prove2.me/submissions/0ae24de9-2c0d-467d-82bf-cae4fabd2564

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_densityProduct_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_exists_G
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_uo_gen
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_rank_of_gram
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_block_count

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {q : ℕ} (hq : 2 ≤ q)
    (htr : ∃ μ : K, μ + star μ ≠ 0)
    (hnorm : ∀ t : K, t ≠ 0 → star t = t → ∃ l : K, star l * l = t)
    (hUO : ∀ (b : ℕ) (J : Matrix (Fin b) (Fin b) K), Jᴴ = J → IsUnit J.det →
      (Nat.card {g : Matrix (Fin b) (Fin b) K // gᴴ * J * g = J} : ℝ) =
        (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b)
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    {α : Type} [Fintype α] [DecidableEq α] (n : ℕ) (J : Matrix (Fin n) (Fin n) K) (T : Matrix α α K)
    (hJ : Jᴴ = J) (hdJ : IsUnit J.det) (hT : Tᴴ = T) (hdT : IsUnit T.det) :
    (Nat.card {X : Matrix (Fin n) α K // Xᴴ * J * X = T} : ℝ) =
      (q : ℝ) ^ ((2 * n * (Fintype.card α) : ℤ) - (Fintype.card α) ^ 2) *
        densP (-1) q ((n : ℤ) - Fintype.card α + 1) n := by
  classical
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rcases lt_or_ge n (Fintype.card α) with hlt | hle
  · rw [densityProduct_eq_zero _ _ _ _ (by omega) (by omega), mul_zero]
    have : IsEmpty {X : Matrix (Fin n) α K // Xᴴ * J * X = T} := by
      constructor
      rintro ⟨X, hX⟩
      have h1 := rank_of_gram J T hdT X hX
      have h2 := rank_le_card_height X
      rw [Fintype.card_fin] at h2
      omega
    simp
  · set a := Fintype.card α with ha
    set D : Matrix (α ⊕ Fin (n - a)) (α ⊕ Fin (n - a)) K := fromBlocks T 0 0 1 with hDdef
    have hD : Dᴴ = D := by rw [hDdef, fromBlocks_conjTranspose]; simp [hT]
    have hdD : IsUnit D.det := by rw [hDdef, det_fromBlocks_zero₂₁]; simpa using hdT
    have hcard : Fintype.card (Fin n) = Fintype.card (α ⊕ Fin (n - a)) := by
      rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]; omega
    obtain ⟨G, G', hGG', hG'G, hG⟩ := exists_G htr hnorm hcard J D hJ hdJ hD hdD
    have e1 : Nat.card {X : Matrix (Fin n) α K // Xᴴ * J * X = T} =
        Nat.card {X : Matrix (α ⊕ Fin (n - a)) α K // Xᴴ * D * X = T} := by
      apply Nat.card_congr
      refine ⟨fun X => ⟨G' * X.1, ?_⟩, fun X => ⟨G * X.1, ?_⟩, ?_, ?_⟩
      · rw [← hG, conjTranspose_mul]
        calc _ = X.1ᴴ * (G * G')ᴴ * J * ((G * G') * X.1) := by
              rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
          _ = T := by rw [hGG']; simpa using X.2
      · rw [conjTranspose_mul]
        calc _ = X.1ᴴ * (Gᴴ * J * G) * X.1 := by simp only [Matrix.mul_assoc]
          _ = T := by rw [hG]; exact X.2
      · intro X; apply Subtype.ext
        show G * (G' * X.1) = X.1
        rw [← Matrix.mul_assoc, hGG', Matrix.one_mul]
      · intro X; apply Subtype.ext
        show G' * (G * X.1) = X.1
        rw [← Matrix.mul_assoc, hG'G, Matrix.one_mul]
    have e2 := block_count hW T (1 : Matrix (Fin (n - a)) (Fin (n - a)) K) hT hdT (by simp) (by simp)
    have u1 := uo_gen hUO D hD hdD
    have u2 := uo_gen hUO (1 : Matrix (Fin (n - a)) (Fin (n - a)) K) (by simp) (by simp)
    rw [← hcard, Fintype.card_fin] at u1
    rw [Fintype.card_fin] at u2
    rw [e1]
    have e3 : (Nat.card {g : Matrix (α ⊕ Fin (n - a)) (α ⊕ Fin (n - a)) K // gᴴ * D * g = D} : ℝ) =
        (Nat.card {X : Matrix (α ⊕ Fin (n - a)) α K // Xᴴ * D * X = T} : ℝ) *
        (Nat.card {d : Matrix (Fin (n - a)) (Fin (n - a)) K // dᴴ * 1 * d = 1} : ℝ) := by
      exact_mod_cast e2
    rw [u1, u2] at e3
    have hsplit := densityProduct_split (-1) q 1 ((n - a : ℕ) : ℤ) n (by omega) (by omega)
    have hpos : 0 < densP (-1) q 1 ((n - a : ℕ) : ℤ) := densityProduct_pos (-1) (Or.inr rfl) q hq _ _ le_rfl
    have hcast : ((n - a : ℕ) : ℤ) = (n : ℤ) - a := by omega
    have hpw : (q : ℝ) ^ (n ^ 2) = (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) * (q : ℝ) ^ ((n - a) ^ 2) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0.ne']
      congr 1
      push_cast [hcast]
      ring
    rw [hsplit, hpw, hcast] at e3
    rw [hcast] at hpos
    have hpp : 0 < (q : ℝ) ^ ((n - a) ^ 2) := by positivity
    have : ((Nat.card {X : Matrix (α ⊕ Fin (n - a)) α K // Xᴴ * D * X = T} : ℝ) -
        (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) * densP (-1) q ((n : ℤ) - a + 1) n) *
        ((q : ℝ) ^ ((n - a) ^ 2) * densP (-1) q 1 ((n : ℤ) - a)) = 0 := by
      linear_combination -e3
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h (by positivity)
end Formalism.FourierDecayAlt.P.S3x5
