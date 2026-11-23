-- Prove2me | solution 1 for Deduction.landau_window_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:29.912134+00:00
-- url     : https://prove2.me/submissions/fbc244de-8a36-4e3d-9dcb-c61903f9c5a6

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauCauchy
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauPoleAsym
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_landauTails
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauKernelMax
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_landauWindowIneq
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauPoleReLe
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauCoeff
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauFinite
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauNearest
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauDichotomy
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LandauGrowthContra
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_landauWindow
import Theorems.Thm_Deduction_landau_coeff
import Theorems.Thm_Deduction_landau_tails
import Theorems.Thm_Deduction_landau_window_ineq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hW : WindowHypU g θ δ) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ k : ℕ, U ≤ k ∧ ∀ γ : ℝ,
      ‖(-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + γ * I) / (k.factorial : ℂ)‖ +
        ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)).re ≤
        C * Real.exp (η * U) / (σ - θ) ^ k := by
  obtain ⟨σ, hσ, C, hC⟩ := landau_tails hδ
  obtain ⟨C₀, hC₀⟩ := hP.growth
  have hC₀0 : 0 ≤ C₀ := by
    have := hC₀ 0 le_rfl
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  refine ⟨σ, hσ, 2 + 2 * C₀ * |C|, fun η hη U₀ => ?_⟩
  obtain ⟨U, hU, R, hR1, hR2, hR3⟩ := hW η hη (max U₀ 1)
  have hU1 : 1 ≤ U := (le_max_right _ _).trans hU
  obtain ⟨k, hk, hk'⟩ := hC U hU1
  refine ⟨U, (le_max_left _ _).trans hU, k, hk, fun γ => ?_⟩
  have h := landau_window_ineq hP.meas hC₀ hσ (by linarith : θ < σ) (by linarith : 0 < U) hR1 hR2 k γ
  rw [landau_coeff hP k (s := (σ : ℂ) + γ * I) (by simpa using hσ),
    landau_coeff hP k (s := (σ : ℂ)) (by simpa using hσ)]
  have hst : 0 < σ - θ := by linarith
  have hstk : 0 < (σ - θ) ^ k := pow_pos hst k
  have hexp : 1 ≤ Real.exp (η * U) := Real.one_le_exp (by positivity)
  have h1 : 2 * (1 / (σ - θ) ^ k) * (∫ u in Icc U ((1 + δ) * U), R u * Real.exp (-θ * u))
      ≤ 2 * (1 / (σ - θ) ^ k) * Real.exp (η * U) :=
    mul_le_mul_of_nonneg_left hR3 (by positivity)
  have h2 : C / σ ^ k ≤ |C| * Real.exp (η * U) / (σ - θ) ^ k := by
    apply div_le_div₀ (by positivity) _ hstk (pow_le_pow_left₀ hst.le (by linarith) k)
    exact (le_abs_self C).trans (le_mul_of_one_le_right (abs_nonneg C) hexp)
  have h3 := mul_le_mul_of_nonneg_left (hk'.trans h2) (by positivity : 0 ≤ 2 * C₀)
  have h4 : (2 + 2 * C₀ * |C|) * Real.exp (η * U) / (σ - θ) ^ k
      = 2 * (1 / (σ - θ) ^ k) * Real.exp (η * U)
        + 2 * C₀ * (|C| * Real.exp (η * U) / (σ - θ) ^ k) := by ring
  linarith
end Deduction
