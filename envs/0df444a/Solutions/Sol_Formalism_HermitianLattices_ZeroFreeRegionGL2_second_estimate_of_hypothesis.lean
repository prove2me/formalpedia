-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.second_estimate_of_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:55.972805+00:00
-- url     : https://prove2.me/submissions/41ddda6c-cdc3-4502-8305-55941f97cff5

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_mul_rpow_log_sq_le_rpow
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_eventually_le_rpow_mul_log_sq
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_log_four_mul_mul_sq
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_four_le_four_mul_sq
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_numerical_estimate_size_conditions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : SecondEstimateOfIntervalHypothesis := by
  intro C₀ c Cρ c₃ hC₀ hc hCρ hc₃ hInt ε δ A integralAdeleSpan C_Y hε hδ hA hcT hCY
  obtain ⟨x₁, hx₁⟩ := numerical_estimate_size_conditions ε δ A integralAdeleSpan (8 * C_Y + 1) C₀ c Cρ hε hδ hA hcT (by positivity) hC₀ hc hCρ
  obtain ⟨x₂, hx₂⟩ := eventually_atTop.mp
    ((eventually_le_rpow_mul_log_sq ε (Real.log 4) hε).and ((eventually_mul_rpow_log_sq_le_rpow ε 6 hε).and (eventually_ge_atTop (1 : ℝ))))
  refine ⟨max x₁ x₂, fun x hx d NE g₁ g₂ m fk Ts hd hd4 hdX hNE hlNE hg₁ hg₂ hlg₁ hlg₂ hm hfk1 hfk2 hTs0 hTs => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hx₂ x (le_trans (le_max_right _ _) hx)
  have hx0 : 0 < x := by linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.one_lt.le
  have hN1 : (1 : ℝ) ≤ (NE : ℝ) := by exact_mod_cast hNE
  have hg1 : (1 : ℝ) ≤ (g₁ : ℝ) := by exact_mod_cast hg₁
  have hg2 : (1 : ℝ) ≤ (g₂ : ℝ) := by exact_mod_cast hg₂
  have hNn : 1 ≤ NE * (g₁ * g₂) ^ 2 := Nat.mul_pos hNE (Nat.pow_pos (Nat.mul_pos hg₁ hg₂))
  have hNr : (1 : ℝ) ≤ ((NE * (g₁ * g₂) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hNn
  have hld : Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
    have := Real.log_le_log (by linarith) hdX
    rwa [X2, Real.log_exp] at this
  have hlN : Real.log ((NE * (g₁ * g₂) ^ 2 : ℕ) : ℝ) = Real.log NE + 2 * (Real.log g₁ + Real.log g₂) := by
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_mul (by positivity) (by positivity)]
    push_cast; ring
  have hlB : Real.log (4 * (d : ℝ) * ((NE * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2) ≤ (8 * C_Y + 1) * x ^ ε := by
    rw [log_four_mul_mul_sq _ _ (by linarith) (by linarith), hlN]
    linarith
  have hfk0 : 0 < fk := by linarith
  obtain ⟨r1, r2, r3⟩ := hx₁ x (le_trans (le_max_left _ _) hx) (4 * (d : ℝ) * ((NE * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2)
    Ts m fk (four_le_four_mul_sq _ _ hd1 hNr) hlB hm hfk1 hfk2 hTs hTs0
  have hh1 : 1 / fk ≤ 1 := by rw [div_le_one hfk0]; exact hfk1
  have hcard := hInt d (NE * (g₁ * g₂) ^ 2) Ts (1 / fk) hd hd4 hNn r1 r2 (by positivity) hh1 r3
  have hm0 : 0 < m := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hm
  have hlTs : 0 < Real.log Ts := lt_of_lt_of_le (by have := Real.rpow_pos_of_pos hx0 ε; positivity) hTs
  have hBpos : 0 < 4 * (d : ℝ) * ((NE * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2 := by
    have := four_le_four_mul_sq _ _ hd1 hNr
    linarith
  have hpos : 0 < c₃ * (1 / fk) * (4 * (d : ℝ) * ((NE * (g₁ * g₂) ^ 2 : ℕ) : ℝ) ^ 2) ^ (-6 : ℝ) * Ts / Real.log Ts := by
    have := Real.rpow_pos_of_pos hBpos (-6 : ℝ)
    positivity
  have hcpos : (0 : ℝ) < ((normPrimes d (NE * (g₁ * g₂) ^ 2) Ts (Ts * (1 + 1 / fk))).card : ℝ) :=
    lt_of_lt_of_le hpos hcard
  obtain ⟨T, hT⟩ := Finset.card_pos.mp (by exact_mod_cast hcpos :
    0 < (normPrimes d (NE * (g₁ * g₂) ^ 2) Ts (Ts * (1 + 1 / fk))).card)
  simp only [normPrimes, Finset.mem_filter, Finset.mem_Icc] at hT
  obtain ⟨⟨_, hTle⟩, hTp, hTlo, hTn⟩ := hT
  refine ⟨T, hTp, hTlo.le, ?_, hTn⟩
  have hhi : 0 ≤ Ts * (1 + 1 / fk) := by positivity
  exact le_trans (by exact_mod_cast hTle) (Nat.floor_le hhi)
end Formalism.HermitianLattices.ZeroFreeRegionGL2
