-- Prove2me | solution 1 for BlackScholesModel.dPlus_expiry_tail_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T16:12:35.108386+00:00
-- url     : https://prove2.me/submissions/77255c9b-64b4-4930-902b-ba75ec77409f

import Mathlib
import Definitions.Def_BlackScholesModel_Core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- The divergent log-moneyness term dominates as remaining time vanishes. -/
theorem solution (K r σ T S : ℝ) (hK : 0 < K)
    (hσ : 0 < σ) (hS : 0 < S) :
    (K < S → Tendsto (fun t => dPlus S K r σ (T - t)) (𝓝[<] T) atTop) ∧
    (S < K → Tendsto (fun t => dPlus S K r σ (T - t)) (𝓝[<] T) atBot) := by
  let a : ℝ := Real.log (S / K) / σ
  let b : ℝ := (r + σ ^ 2 / 2) / σ
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hroot : Tendsto (fun t : ℝ => Real.sqrt (T - t))
      (𝓝[<] T) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => Real.sqrt (T - t)) := by
      fun_prop
    convert hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1 <;>
      simp
  have hrootPos : Tendsto (fun t : ℝ => Real.sqrt (T - t))
      (𝓝[<] T) (𝓝[>] 0) := by
    apply (tendsto_nhdsWithin_iff).2
    constructor
    · exact hroot
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Real.sqrt_pos.2 (sub_pos.mpr ht)
  have hinv : Tendsto (fun t : ℝ => (Real.sqrt (T - t))⁻¹)
      (𝓝[<] T) atTop :=
    tendsto_inv_nhdsGT_zero.comp hrootPos
  have hsmall : Tendsto (fun t : ℝ => b * Real.sqrt (T - t))
      (𝓝[<] T) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hroot
  have hrepr : (fun t : ℝ => dPlus S K r σ (T - t)) =ᶠ[𝓝[<] T]
      (fun t => a * (Real.sqrt (T - t))⁻¹ +
        b * Real.sqrt (T - t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hτ : 0 < T - t := sub_pos.mpr ht
    have hsqrt0 : Real.sqrt (T - t) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hτ)
    have hsqrt : Real.sqrt (T - t) ^ 2 = T - t :=
      Real.sq_sqrt (le_of_lt hτ)
    dsimp [a, b, dPlus]
    calc
      (Real.log (S / K) + (r + σ ^ 2 / 2) * (T - t)) /
          (σ * Real.sqrt (T - t)) =
        (Real.log (S / K) + (r + σ ^ 2 / 2) * Real.sqrt (T - t) ^ 2) /
          (σ * Real.sqrt (T - t)) := by rw [hsqrt]
      _ = (Real.log (S / K) / σ) * (Real.sqrt (T - t))⁻¹ +
          ((r + σ ^ 2 / 2) / σ) * Real.sqrt (T - t) := by
            field_simp [hσ0, hsqrt0]
  constructor
  · intro hSK
    have hratio : 1 < S / K := by
      rw [one_lt_div hK]
      exact hSK
    have ha : 0 < a :=
      div_pos (Real.log_pos hratio) hσ
    have hbig : Tendsto (fun t : ℝ => a * (Real.sqrt (T - t))⁻¹)
        (𝓝[<] T) atTop :=
      hinv.const_mul_atTop ha
    have hh := hbig.atTop_add hsmall
    exact hh.congr' hrepr.symm
  · intro hSK
    have hratio : S / K < 1 := by
      rw [div_lt_one hK]
      exact hSK
    have ha : a < 0 :=
      div_neg_of_neg_of_pos
        ((Real.log_neg_iff (div_pos hS hK)).2 hratio) hσ
    have hbig : Tendsto (fun t : ℝ => a * (Real.sqrt (T - t))⁻¹)
        (𝓝[<] T) atBot :=
      hinv.const_mul_atTop_of_neg ha
    have hh := hbig.atBot_add hsmall
    exact hh.congr' hrepr.symm