-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:35:05.013806+00:00
-- url     : https://prove2.me/submissions/1d4c3227-9c23-4d8b-8450-5d61aa4fad78

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open PI.UpqRep
open Formalism.FourierDecayAlt.P.TranslationBesselVanishing
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TranslationBesselVanishing
theorem _root_.solution {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hds : IsDSHpk k r ε lam σ) {h g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : hᴴ * Hpk k r * h = Hpk k r) (hg : gᴴ * Hpk k r * g = Hpk k r) :
    σ (h * g) = (σ h).comp (σ g) := by
  obtain ⟨P, hP, hDS⟩ := hds
  have hmul := hDS.2.2.1.1.2
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have hsP : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp hPu
  have hPs : P * star P = 1 := Matrix.mem_unitaryGroup_iff.mp hPu
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv hsP
  have hJ : Jm ε = P * Hpk k r * star P := by
    rw [← hP.1.2, ← Matrix.star_eq_conjTranspose]
    calc Jm ε = (P * star P) * Jm ε * (P * star P) := by rw [hPs, Matrix.one_mul, Matrix.mul_one]
      _ = P * (star P * Jm ε * P) * star P := by simp only [Matrix.mul_assoc]
  have memJ : ∀ x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      xᴴ * Hpk k r * x = Hpk k r → P * x * P⁻¹ ∈ UJset ε := by
    intro x hx
    have hx' : star x * Hpk k r * x = Hpk k r := by rw [Matrix.star_eq_conjTranspose]; exact hx
    show (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = Jm ε
    rw [hinv, hJ, ← Matrix.star_eq_conjTranspose]
    calc star (P * x * star P) * (P * Hpk k r * star P) * (P * x * star P)
        = P * (star x * (star P * P) * Hpk k r * (star P * P) * x) * star P := by
          simp only [star_mul, star_star, Matrix.mul_assoc]
      _ = P * (star x * Hpk k r * x) * star P := by simp only [hsP, Matrix.mul_one]
      _ = P * Hpk k r * star P := by rw [hx']
  have key : ∀ x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P⁻¹ * (P * x * P⁻¹) * P = x := by
    intro x
    rw [hinv]
    calc star P * (P * x * star P) * P = (star P * P) * x * (star P * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hsP, Matrix.one_mul, Matrix.mul_one]
  have hprod : (P * h * P⁻¹) * (P * g * P⁻¹) = P * (h * g) * P⁻¹ := by
    rw [hinv]
    calc P * h * star P * (P * g * star P) = P * h * (star P * P) * g * star P := by
          simp only [Matrix.mul_assoc]
      _ = P * (h * g) * star P := by rw [hsP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h1 := hmul (P * h * P⁻¹) (memJ h hh) (P * g * P⁻¹) (memJ g hg)
  dsimp only at h1
  rw [hprod, key, key, key] at h1
  exact h1
end Formalism.FourierDecayAlt.P.TranslationBesselVanishing
