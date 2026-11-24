-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.norm_one_estimate_of_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:14.239838+00:00
-- url     : https://prove2.me/submissions/2c16089b-3a18-463e-af1b-bbea5407e131

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NormOneEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_choice_of_exponent_constant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : Formalism.HermitianLattices.ZeroFreeRegionGL2.PrimeBoundOfUptoHyp := by
  intro C₀ c Cρ c₃ hC₀ hc hCρ hc₃ hU C hC
  obtain ⟨C₁, hC₁, hN⟩ := choice_of_exponent_constant C C₀ c Cρ c₃ hC hC₀ hc hCρ hc₃
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le hC₀ hC₁
  refine ⟨(2 * C + 3) * C₁, by positivity, ?_⟩
  intro d NE M₀ J hd hd4 hdN hM hMC hJC
  have hd3 : 3 ≤ d := by omega
  have hNE12 : 12 ≤ NE := by omega
  have hNEr : (12 : ℝ) ≤ (NE : ℝ) := by exact_mod_cast hNE12
  have hNE0 : (0 : ℝ) < (NE : ℝ) := by linarith
  have hNE1 : (1 : ℝ) ≤ (NE : ℝ) := by linarith
  have hMr : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM
  have hdr : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd3
  have hdNr : 4 * (d : ℝ) ≤ (NE : ℝ) := by exact_mod_cast hdN
  set B : ℝ := 4 * (d : ℝ) * (((M₀ * NE : ℕ) : ℕ) : ℝ) ^ 2 with hBdef
  have hNcast : (((M₀ * NE : ℕ) : ℕ) : ℝ) = (M₀ : ℝ) * (NE : ℝ) := by push_cast; ring
  have hMN : (NE : ℝ) ≤ (M₀ : ℝ) * (NE : ℝ) := by nlinarith
  have hBlow : (NE : ℝ) ≤ B := by
    rw [hBdef, hNcast]
    have h1 : (NE : ℝ) ^ 2 ≤ ((M₀ : ℝ) * (NE : ℝ)) ^ 2 := pow_le_pow_left₀ hNE0.le hMN 2
    nlinarith
  have hB12 : (12 : ℝ) ≤ B := le_trans hNEr hBlow
  have hB0 : (0 : ℝ) < B := by linarith
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hBup : B ≤ (NE : ℝ) ^ (2 * C + 3) := by
    have e : (NE : ℝ) ^ (2 * C + 3) = (NE : ℝ) * (((NE : ℝ) ^ C) * (NE : ℝ)) ^ 2 := by
      have e1 : (2 * C + 3) = 1 + (C + 1) * (2 : ℕ) := by push_cast; ring
      rw [e1, Real.rpow_add hNE0, Real.rpow_one, Real.rpow_mul hNE0.le, Real.rpow_natCast,
        Real.rpow_add hNE0, Real.rpow_one]
    rw [e, hBdef, hNcast]
    have h1 : (M₀ : ℝ) * (NE : ℝ) ≤ (NE : ℝ) ^ C * (NE : ℝ) := mul_le_mul_of_nonneg_right hMC hNE0.le
    have h2 : ((M₀ : ℝ) * (NE : ℝ)) ^ 2 ≤ ((NE : ℝ) ^ C * (NE : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    exact mul_le_mul hdNr h2 (by positivity) hNE0.le
  obtain ⟨hrho, hcount⟩ := hN B hB12
  have hN1 : 1 ≤ M₀ * NE := by
    have : 1 ≤ NE := by omega
    exact Nat.mul_pos hM this
  have hU' := hU d (M₀ * NE) (B ^ C₁) hd hd4 hN1
    (Real.rpow_le_rpow_of_exponent_le hB1 hC₁) hrho
  have hcard : (J : ℝ) ≤ ((Formalism.HermitianLattices.ZeroFreeRegionGL2.normPrimes d (M₀ * NE) 0 (B ^ C₁)).card : ℝ) := by
    have h1 : (NE : ℝ) ^ C ≤ B ^ C := Real.rpow_le_rpow hNE0.le hBlow hC.le
    linarith
  have hcard' : J ≤ (Formalism.HermitianLattices.ZeroFreeRegionGL2.normPrimes d (M₀ * NE) 0 (B ^ C₁)).card := by exact_mod_cast hcard
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq hcard'
  refine ⟨S, hSc, ?_⟩
  intro p hp
  have hp' := hS hp
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.normPrimes at hp'
  simp only [Finset.mem_filter, Finset.mem_Icc] at hp'
  obtain ⟨⟨_, hple⟩, hpp, _, hpn⟩ := hp'
  refine ⟨hpp, hpn, ?_⟩
  have hX0 : 0 ≤ B ^ C₁ := (Real.rpow_pos_of_pos hB0 _).le
  have h1 : (p : ℝ) ≤ B ^ C₁ := le_trans (by exact_mod_cast hple) (Nat.floor_le hX0)
  have h2 : B ^ C₁ ≤ ((NE : ℝ) ^ (2 * C + 3)) ^ C₁ := Real.rpow_le_rpow hB0.le hBup hC₁0.le
  rw [← Real.rpow_mul hNE0.le] at h2
  exact le_trans h1 h2
end Formalism.HermitianLattices.ZeroFreeRegionGL2
