-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.far_region_negligible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:45.985152+00:00
-- url     : https://prove2.me/submissions/836cb4e3-9e3d-4f90-9c5e-4b3103425551

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_le_rpow_two_mul
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ydat_facts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : FarNegligible := by
  intro C C₁ c m hC hC₁ hc
  refine ⟨16 * ((2 * C + C₁) * m + 2 + c), by positivity, ?_⟩
  intro n q f rd g b x hn hq hf hrd hg hb hx
  obtain ⟨hY, hnY, hfY, hrdY, hgY, hbY⟩ := ydat_facts hn hf hrd hg hb
  generalize Ydat n f rd g b = Y at *
  have hY0 : 0 < Y := by linarith
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hlog : 1 / 2 ≤ Real.log Y := by
    have h1 := Real.log_two_gt_d9
    have h2 : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) hY
    linarith
  have hlogn : Real.log n ≤ Real.log Y := Real.log_le_log (by linarith) hnY
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn'
  have h1 : C / Y ^ (-(C₁ * q)) ≤ Real.exp (Real.log Y * (2 * C + C₁ * q)) := by
    rw [Real.rpow_neg hY0.le, div_inv_eq_mul, ← Real.rpow_def_of_pos hY0, Real.rpow_add hY0]
    have := le_rpow_two_mul hY (by linarith : 0 ≤ C)
    gcongr
  have h2 : 2 * (f:ℝ) ≤ Real.exp (Real.log Y * 2) := by
    rw [← Real.rpow_def_of_pos hY0, Real.rpow_two]
    nlinarith
  have h0 : 0 ≤ C / Y ^ (-(C₁ * q)) := by positivity
  calc (C / Y ^ (-(C₁ * q))) ^ (m * n ^ 2 * f) * (2 * f) * Real.exp (-(x / 16))
      ≤ (Real.exp (Real.log Y * (2 * C + C₁ * q))) ^ (m * n ^ 2 * f) * Real.exp (Real.log Y * 2)
          * Real.exp (-(x / 16)) := by gcongr
    _ = Real.exp (((m * n ^ 2 * f : ℕ) : ℝ) * (Real.log Y * (2 * C + C₁ * q)) + Real.log Y * 2
          + -(x / 16)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        push_cast
        generalize Real.log Y = ℓ at *
        generalize Real.log (n:ℝ) = ln at *
        set u := (n:ℝ) ^ 2 * q * f with hu
        have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
        have u1 : (n:ℝ) ^ 2 * f ≤ u := by
          rw [hu]
          calc (n:ℝ) ^ 2 * f = (n:ℝ) ^ 2 * 1 * f := by ring
            _ ≤ _ := by gcongr
        have u2 : (n:ℝ) * f ≤ (n:ℝ) ^ 2 * f := by
          have : (n:ℝ) ≤ (n:ℝ) ^ 2 := by nlinarith
          gcongr
        have u3 : 1 ≤ (n:ℝ) * f := by nlinarith
        have hx' : ((2 * C + C₁) * m + 2 + c) * (u * ℓ) ≤ x / 16 := by
          have : 16 * ((2 * C + C₁) * m + 2 + c) * (n:ℝ) ^ 2 * q * f * ℓ
              = 16 * (((2 * C + C₁) * m + 2 + c) * (u * ℓ)) := by rw [hu]; ring
          linarith
        have t1 : (m:ℝ) * (n:ℝ) ^ 2 * f * (ℓ * (2 * C + C₁ * q)) ≤ (2 * C + C₁) * m * (u * ℓ) := by
          have e : (m:ℝ) * (n:ℝ) ^ 2 * f * (ℓ * (2 * C + C₁ * q))
              = m * ℓ * (2 * C * ((n:ℝ) ^ 2 * f) + C₁ * u) := by rw [hu]; ring
          rw [e]
          calc (m:ℝ) * ℓ * (2 * C * ((n:ℝ) ^ 2 * f) + C₁ * u) ≤ m * ℓ * (2 * C * u + C₁ * u) := by
                gcongr
            _ = _ := by ring
        have t2 : ℓ * 2 ≤ 2 * (u * ℓ) := by
          have : 1 ≤ u := by linarith
          nlinarith
        have t3 : c * n * f * ln ≤ c * (u * ℓ) := by
          calc c * n * f * ln = c * ((n * f) * ln) := by ring
            _ ≤ c * (u * ℓ) := by
              gcongr
              linarith
        nlinarith
end Formalism.HermitianLatticeCounting.P
