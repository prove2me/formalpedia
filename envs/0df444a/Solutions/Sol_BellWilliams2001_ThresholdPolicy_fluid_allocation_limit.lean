-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.fluid_allocation_limit
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:30:37.117804+00:00
-- url     : https://prove2.me/submissions/6d4db9b3-b080-4c91-9611-923dc293d531

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_admissible_discounted_cost_aemeasurable
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_fluid_allocations_from_vanishing_queues
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_fluid_queue_vanishes_from_bounded_cost
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_queue_second_moment

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology Set
open scoped ENNReal

private theorem exp_poly_lintegral_ne_top {γ C : ℝ} (hγ : 0 < γ) (hC : 0 ≤ C) (p : ℕ) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-γ*t) * (1+C*(1+t)^p))) ≠ ⊤ := by
  have h₁ : IntegrableOn (fun t : ℝ => Real.exp (-γ*t)) (Ioi (0:ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hγ) 0
  have h₂ : IntegrableOn (fun t : ℝ => Real.exp (-γ*t) * t^p) (Ioi (0:ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (p:ℝ)) (b := γ) (p := (1:ℝ))
      (by have := Nat.cast_nonneg (α := ℝ) p; linarith) one_pos hγ
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul, mul_comm] using h
  have h₃ : IntegrableOn (fun t : ℝ => Real.exp (-γ*t) * (1+C*(1+t)^p)) (Ioi (0:ℝ)) := by
    have h := h₁.add ((h₁.const_mul (C * 2^p)).add (h₂.const_mul (C * 2^p)))
    refine h.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    have hp : (1+t)^p ≤ 2^p + 2^p*t^p := by
      by_cases hsmall : t ≤ 1
      · exact (pow_le_pow_left₀ (by positivity) (by linarith) p).trans
          (le_add_of_nonneg_right (by positivity))
      · have hb : 1+t ≤ 2*t := by linarith
        exact ((pow_le_pow_left₀ (by positivity) hb p).trans_eq (mul_pow _ _ _)).trans
          (le_add_of_nonneg_left (by positivity))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hc := mul_le_mul_of_nonneg_left hp hC
    have he := mul_le_mul_of_nonneg_left (add_le_add_left hc 1) (Real.exp_nonneg (-γ*t))
    change Real.exp (-γ*t) * (1+C*(1+t)^p) ≤
      Real.exp (-γ*t) + (C * 2^p * Real.exp (-γ*t) + C * 2^p * (Real.exp (-γ*t) * t^p))
    calc
      _ = Real.exp (-γ*t) * (C*(1+t)^p + 1) := by ring
      _ ≤ Real.exp (-γ*t) * (C*(2^p+2^p*t^p) + 1) := he
      _ = _ := by ring
  have hNon : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun t => Real.exp (-γ*t) * (1+C*(1+t)^p)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    show 0 ≤ Real.exp (-γ*t) * (1+C*(1+t)^p)
    positivity
  exact (hasFiniteIntegral_iff_ofReal hNon).1 h₃.hasFiniteIntegral |>.ne


set_option maxHeartbeats 1100000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ Tstar : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (Tstar n) ∧ M.IsThreshold c n (Tstar n)) →
      UocInProb M.P (fun n ω t => M.Tbar n (Tstar n) ω t) M.fluidAllocation := by
  letI : IsProbabilityMeasure M.P := M.isProb
  obtain ⟨c₀,hc₀,hM⟩ := threshold_queue_second_moment M
  refine ⟨c₀,hc₀,fun c hc T hT => ?_⟩
  obtain ⟨C,hC,p,hMom⟩ := hM c hc T hT
  have hAd : ∀ᶠ n in atTop, M.IsAdmissible n (T n) := by
    have h := (Real.tendsto_log_atTop.comp M.r_tendsto).const_mul_atTop (hc₀.trans hc)
    exact (h.eventually_ge_atTop (1:ℝ)).mono (fun n hn => (hT n ((Nat.one_le_floor_iff _).mpr hn)).1)
  let ν := volume.restrict (Ioi (0:ℝ))
  let D (t : ℝ) := ENNReal.ofReal (Real.exp (-M.gamma*t)*(1+C*(1+t)^p))
  let B := ∫⁻ t, D t ∂ν
  have hB : B ≠ ⊤ := exp_poly_lintegral_ne_top M.gamma_pos hC p
  have hcB : ∀ᶠ n in atTop, M.cost n (T n) ≤ ENNReal.ofReal B.toReal := by
    filter_upwards [hAd,hMom] with n hn hm
    let f (ω : Ω) (t : ℝ) := ENNReal.ofReal (Real.exp (-M.gamma*t)*∑ k, M.h k*M.Qhat n (T n) ω t k)
    have hf : AEMeasurable (Function.uncurry f) (M.P.prod ν) :=
      (admissible_discounted_cost_aemeasurable M n (T n) hn).1
    change (∫⁻ ω, ∫⁻ t, f ω t ∂ν ∂M.P) ≤ ENNReal.ofReal B.toReal
    rw [lintegral_lintegral_swap hf, ENNReal.ofReal_toReal hB]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    let a (ω : Ω) := ∑ k, M.h k*M.Qhat n (T n) ω t k
    have hPt (x : ℝ) : ENNReal.ofReal x ≤ 1+ENNReal.ofReal x^2 := by
      by_cases hx : 0 ≤ x
      · have hi : x ≤ 1+x^2 := by nlinarith [sq_nonneg (x-1)]
        simpa [ENNReal.ofReal_add zero_le_one (sq_nonneg x),ENNReal.ofReal_pow hx] using ENNReal.ofReal_le_ofReal hi
      · simp [ENNReal.ofReal_eq_zero.2 (le_of_not_ge hx)]
    have hInt : (∫⁻ ω, ENNReal.ofReal (a ω) ∂M.P) ≤ 1+ENNReal.ofReal (C*(1+t)^p) := by
      calc
        _ ≤ ∫⁻ ω, 1+ENNReal.ofReal (a ω)^2 ∂M.P := lintegral_mono (fun ω => hPt _)
        _ = 1+(∫⁻ ω, ENNReal.ofReal (a ω)^2 ∂M.P) := by
          rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one]
        _ ≤ _ := add_le_add_right (hm t ht0) _
    have hex := Real.exp_nonneg (-M.gamma*t)
    have hP : 0 ≤ C*(1+t)^p := by positivity
    simp only [f,D,a,ENNReal.ofReal_mul hex,ENNReal.ofReal_add zero_le_one hP,ENNReal.ofReal_one]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_right hInt _
  have hq := fluid_queue_vanishes_from_bounded_cost M id tendsto_id T hAd _ ENNReal.toReal_nonneg hcB
  exact (fluid_allocations_from_vanishing_queues M id tendsto_id T hAd hq).1
