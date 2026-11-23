-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HessianScalingIntegrals.root_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:13.787798+00:00
-- url     : https://prove2.me/submissions/32c6a82c-f7d1-4701-9c4b-820ca347b8fd

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals
import Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_ball_piece
import Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_hess_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_psi_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_HessianScalingIntegrals_amp_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HessianScalingIntegrals
variable {K : Type} [CommRing K]
open Classical
namespace Formalism.FourierDecayAlt.P.HessianScalingIntegrals
theorem _root_.solution [TopologicalSpace K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
    (hγ : IsGamma R ψ m γ) (Λ₁ : AddSubgroup K) (B Λ : Submodule R K)
    (hB : IsLat B.toAddSubgroup) (hΛ : IsLat Λ.toAddSubgroup) (hΛB : Λ ≤ B)
    (hBΛ₁ : ∀ b ∈ B, b ∈ Λ₁)
    (A : (Fin m → K) → ℂ) (hA : LatInvN Λ₁ A) (t z : Kˣ) (D : K) (hD : (z : K) ^ (m + 1) = D)
    (hmod : 0 < modK R (z : K) ∧ 0 < modK R (t : K) ∧
      modK R ((z : K) * (t : K)) = modK R (z : K) * modK R (t : K))
    (hadm : GaussAdm ψ B.toAddSubgroup (hessM m (z * t)))
    (hmorse : ∃ φ : (Fin m → K) → (Fin m → K),
        Set.BijOn φ {ξ | ∀ k, ξ k ∈ B} {ξ | ∀ k, ξ k ∈ B} ∧
        (∀ Λ : Submodule R K, Λ ≤ B → ∀ ξ η : Fin m → K, (∀ k, ξ k ∈ B) → (∀ k, η k ∈ B) →
          ((∀ k, φ ξ k - φ η k ∈ Λ) ↔ ∀ k, ξ k - η k ∈ Λ)) ∧
        ∀ ξ : Fin m → K, (∀ k, ξ k ∈ B) →
          (∀ k, IsUnit ((z : K) + φ ξ k)) ∧
          g0 ((z : K) ^ (m + 1)) (fun k => (z : K) + φ ξ k) =
            ((m + 1 : ℕ) : K) * (z : K) + Ring.inverse 2 * (ξ ⬝ᵥ (hessM m z *ᵥ ξ)))
    (hinv : LatInvN Λ.toAddSubgroup (fun x : Fin m → K => if ∀ k, x k - (z : K) ∈ B then
      A x * ψ (g0 D x * ((t⁻¹ : Kˣ) : K)) else 0)) :
    intK R Λ.toAddSubgroup m (fun x : Fin m → K => if ∀ k, x k - (z : K) ∈ B then
      A x * ψ (g0 D x * ((t⁻¹ : Kˣ) : K)) else 0) =
      ((modK R (t : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
        (γ (z * t) * ((modK R ((m + 1 : ℕ) : K) ^ (-(1 : ℝ) / 2) *
            modK R (z : K) ^ ((m : ℝ) / 2) : ℝ) : ℂ) *
          ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) * A (fun _ => (z : K))) := by
  subst hD
  by_cases hA0 : A (fun _ => (z : K)) = 0
  · have h0 : (fun x : Fin m → K => if ∀ k, x k - (z : K) ∈ B then
        A x * ψ (g0 ((z : K) ^ (m + 1)) x * ((t⁻¹ : Kˣ) : K)) else 0) = fun _ => 0 := by
      funext x
      split_ifs with h
      · rw [amp_const Λ₁ A hA z x (fun k => hBΛ₁ _ (h k)), hA0, zero_mul]
      · rfl
    rw [h0, hA0]
    simp [intK]
  · obtain ⟨φ, hbij, hcos, hval⟩ := hmorse
    set c : ℂ := A (fun _ => (z : K)) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t⁻¹ : Kˣ) : K)) with hc
    have hc0 : c ≠ 0 := mul_ne_zero hA0 (psi_ne_zero ψ _)
    obtain ⟨hi, he⟩ := ball_piece R m B.toAddSubgroup Λ.toAddSubgroup hΛB (z : K) φ hbij
      (hcos Λ hΛB) _ (fun ξ => c * gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ) hinv
      (fun x hx => if_neg hx)
      (fun ξ hξ => by
        have : gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ = 0 := if_neg hξ
        rw [this, mul_zero])
      (fun ξ hξ => by
        have h1 : ∀ k, (z : K) + φ ξ k - (z : K) ∈ B := fun k => by
          have : φ ξ k ∈ B := hbij.mapsTo hξ k
          simpa using this
        have h2 : gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ =
            ψ (Ring.inverse 2 * (ξ ⬝ᵥ (hessM m (z * t) *ᵥ ξ))) := if_pos hξ
        rw [h2]
        simp only []
        rw [if_pos h1, amp_const Λ₁ A hA z _ (fun k => hBΛ₁ _ (h1 k)), (hval ξ hξ).2, hc, mul_assoc,
          ← AddChar.map_add_eq_mul, hess_scale, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        congr 2
        ring)
    have hi' : LatInvN Λ.toAddSubgroup (gaussF ψ B.toAddSubgroup (hessM m (z * t))) := by
      intro ξ l hl
      exact mul_left_cancel₀ hc0 (hi ξ l hl)
    rw [he]
    have h3 : intK R Λ.toAddSubgroup m (fun ξ => c * gaussF ψ B.toAddSubgroup (hessM m (z * t)) ξ) =
        c * intK R Λ.toAddSubgroup m (gaussF ψ B.toAddSubgroup (hessM m (z * t))) := by
      unfold intK
      rw [mul_left_comm]
      congr 1
      have := smul_finsum c (fun y : Fin m → K ⧸ Λ.toAddSubgroup =>
        gaussF ψ B.toAddSubgroup (hessM m (z * t)) (fun i => Quotient.out (y i)))
      simpa [smul_eq_mul] using this.symm
    rw [h3, hγ.2.2 (z * t) _ _ hB hΛ hadm hi', Units.val_mul, hmod.2.2,
      Real.mul_rpow hmod.1.le hmod.2.1.le, hc]
    push_cast
    ring
end Formalism.FourierDecayAlt.P.HessianScalingIntegrals
