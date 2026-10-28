-- Prove2me | solution 1 for CoherenceTracking.Dephasing.field_strength
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:26:31.630987+00:00
-- url     : https://prove2.me/submissions/8acace2d-ec6c-4f5c-9f47-e42c5c328abb

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

open CoherenceTracking.Dephasing


theorem solution (γ : ℝ) (hγ : 0 < γ) (v0 : BVec) (hc : 0 < initCoherence v0) :
    (∀ (ω0 : ℝ → ℝ), ∀ t ∈ Set.Ico 0 (breakdownTime γ v0),
      trackingFields γ v0 ω0 t 1 ^ 2 + trackingFields γ v0 ω0 t 2 ^ 2 =
        (γ ^ 2 + ω0 t ^ 2) * initCoherence v0 / (v0 2 ^ 2 - 2 * γ * initCoherence v0 * t)) ∧
    (∀ w0 : ℝ, StrictMonoOn
      (fun t => trackingFields γ v0 (fun _ => w0) t 1 ^ 2 +
        trackingFields γ v0 (fun _ => w0) t 2 ^ 2)
      (Set.Ico 0 (breakdownTime γ v0))) := by
  have key : ∀ (ω0 : ℝ → ℝ), ∀ t ∈ Set.Ico 0 (breakdownTime γ v0),
      trackingFields γ v0 ω0 t 1 ^ 2 + trackingFields γ v0 ω0 t 2 ^ 2 =
        (γ ^ 2 + ω0 t ^ 2) * initCoherence v0 / (v0 2 ^ 2 - 2 * γ * initCoherence v0 * t) := by
    intro ω0 t ht
    have h2 : 0 < 2 * γ * initCoherence v0 := by positivity
    have htb : t * (2 * γ * initCoherence v0) < v0 2 ^ 2 := by
      have := ht.2
      unfold breakdownTime at this
      exact (lt_div_iff₀ h2).mp this
    have hD : 0 < v0 2 ^ 2 - 2 * γ * initCoherence v0 * t := by nlinarith [ht.1]
    have hv2 : v0 2 ≠ 0 := by
      intro h; rw [h] at htb; nlinarith [ht.1]
    have hs : Real.sign (v0 2) ^ 2 = 1 := by
      rcases lt_or_gt_of_ne hv2 with h | h
      · rw [Real.sign_of_neg h]; norm_num
      · rw [Real.sign_of_pos h]; norm_num
    have e1 : trackingFields γ v0 ω0 t 1 = Real.sign (v0 2) * (-γ * v0 1 + ω0 t * v0 0) /
        √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * t) := rfl
    have e2 : trackingFields γ v0 ω0 t 2 = Real.sign (v0 2) * (-γ * v0 0 - ω0 t * v0 1) /
        √(v0 2 ^ 2 - 2 * γ * initCoherence v0 * t) := rfl
    rw [e1, e2]
    rw [div_pow, div_pow, mul_pow, mul_pow, hs, Real.sq_sqrt hD.le]
    unfold initCoherence
    field_simp
    ring
  refine ⟨key, fun w0 => ?_⟩
  intro a ha b hb hab
  simp only
  rw [key (fun _ => w0) a ha, key (fun _ => w0) b hb]
  have h2 : 0 < 2 * γ * initCoherence v0 := by positivity
  have htb : b * (2 * γ * initCoherence v0) < v0 2 ^ 2 := by
    have := hb.2
    unfold breakdownTime at this
    exact (lt_div_iff₀ h2).mp this
  have hDb : 0 < v0 2 ^ 2 - 2 * γ * initCoherence v0 * b := by nlinarith
  apply div_lt_div_of_pos_left (by positivity) hDb
  nlinarith
