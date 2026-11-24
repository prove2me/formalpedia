-- Prove2me | solution 1 for FaulhuberTFA.crossAmbiguity_covariance
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:24:02.401211+00:00
-- url     : https://prove2.me/submissions/c285d39a-38db-4ac3-be49-4fc1453c8a23

import Mathlib
import Definitions.Def_FaulhuberTFA_Basic

set_option autoImplicit false

open MeasureTheory Complex
open scoped InnerProductSpace

namespace FaulhuberTFA

lemma cv_ePhase_add (a b : ℝ) : ePhase (a + b) = ePhase a * ePhase b := by
  unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma cv_conj_ePhase (s : ℝ) : starRingEnd ℂ (ePhase s) = ePhase (-s) := by
  unfold ePhase; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

end FaulhuberTFA

open FaulhuberTFA in
theorem solution {d : ℕ} {f g : Rd d → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (x ω ξ₁ ξ₂ η₁ η₂ : Rd d) :
    crossAmbiguity (modul η₁ (transl ξ₁ f)) (modul η₂ (transl ξ₂ g)) x ω =
      ePhase (⟪x, η₁ + η₂⟫_ℝ / 2) * ePhase (-⟪ω, ξ₁ + ξ₂⟫_ℝ / 2) * ePhase (⟪η₁ - η₂, ξ₁ + ξ₂⟫_ℝ / 2) *
        crossAmbiguity f g (x - ξ₁ + ξ₂) (ω - η₁ + η₂) := by
  unfold crossAmbiguity modul transl
  rw [← integral_const_mul]
  rw [← integral_add_right_eq_self (μ := volume) _ ((1 / 2 : ℝ) • (ξ₁ + ξ₂))]
  congr 1; funext t
  have h1 : t + (1 / 2 : ℝ) • (ξ₁ + ξ₂) + (1 / 2 : ℝ) • x - ξ₁
      = t + (1 / 2 : ℝ) • (x - ξ₁ + ξ₂) := by module
  have h2 : t + (1 / 2 : ℝ) • (ξ₁ + ξ₂) - (1 / 2 : ℝ) • x - ξ₂
      = t - (1 / 2 : ℝ) • (x - ξ₁ + ξ₂) := by module
  rw [h1, h2, map_mul, cv_conj_ePhase]
  set c := (1 / 2 : ℝ) • (ξ₁ + ξ₂) with hc
  have h3 : ⟪η₁, t + c + (1 / 2 : ℝ) • x⟫_ℝ + -⟪η₂, t + c - (1 / 2 : ℝ) • x⟫_ℝ + -⟪ω, t + c⟫_ℝ
      = ⟪x, η₁ + η₂⟫_ℝ / 2 + -⟪ω, ξ₁ + ξ₂⟫_ℝ / 2 + ⟪η₁ - η₂, ξ₁ + ξ₂⟫_ℝ / 2
        + -⟪ω - η₁ + η₂, t⟫_ℝ := by
    simp only [hc, inner_add_right, inner_sub_right, inner_smul_right,
      inner_sub_left, real_inner_comm x, real_inner_comm t]
    ring
  have : ePhase ⟪η₁, t + c + (1 / 2 : ℝ) • x⟫_ℝ * f (t + (1 / 2 : ℝ) • (x - ξ₁ + ξ₂)) *
        (ePhase (-⟪η₂, t + c - (1 / 2 : ℝ) • x⟫_ℝ) * starRingEnd ℂ (g (t - (1 / 2 : ℝ) • (x - ξ₁ + ξ₂)))) *
        ePhase (-⟪ω, t + c⟫_ℝ)
      = ePhase (⟪η₁, t + c + (1 / 2 : ℝ) • x⟫_ℝ + -⟪η₂, t + c - (1 / 2 : ℝ) • x⟫_ℝ + -⟪ω, t + c⟫_ℝ)
        * (f (t + (1 / 2 : ℝ) • (x - ξ₁ + ξ₂)) * starRingEnd ℂ (g (t - (1 / 2 : ℝ) • (x - ξ₁ + ξ₂)))) := by
    rw [cv_ePhase_add, cv_ePhase_add]; ring
  rw [this, h3, cv_ePhase_add, cv_ePhase_add, cv_ePhase_add]; ring
