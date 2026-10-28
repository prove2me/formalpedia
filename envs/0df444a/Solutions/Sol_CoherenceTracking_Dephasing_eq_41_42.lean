-- Prove2me | solution 1 for CoherenceTracking.Dephasing.eq_41_42
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:31:55.276567+00:00
-- url     : https://prove2.me/submissions/87917645-02cc-469d-9ba6-bc5cd58625c1

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

open CoherenceTracking.Dephasing in
theorem solution (γ : ℝ) (hγ : 0 < γ) (v0 : BVec) (hz : v0 2 ≠ 0) (hc : 0 < initCoherence v0) :
    trackedBloch γ v0 0 = v0 ∧
    (∀ ω0 : ℝ → ℝ, ∀ t ∈ Set.Ico 0 (breakdownTime γ v0),
        HasDerivAt (trackedBloch γ v0)
          ((blochMatrix γ (trackingFields γ v0 ω0 t)).mulVec (trackedBloch γ v0 t)) t) ∧
    (∀ (ω : ℝ → Fin 3 → ℝ), ∀ t ∈ Set.Ico 0 (breakdownTime γ v0),
        HasDerivAt (trackedBloch γ v0) ((blochMatrix γ (ω t)).mulVec (trackedBloch γ v0 t)) t →
        ω t 1 = trackingFields γ v0 (fun s => ω s 0) t 1 ∧
        ω t 2 = trackingFields γ v0 (fun s => ω s 0) t 2) := by
  set s := Real.sign (v0 2) with hs
  set c := initCoherence v0 with hcdef
  have hs2 : s * s = 1 := by
    rcases lt_or_gt_of_ne hz with h | h
    · rw [hs, Real.sign_of_neg h]; norm_num
    · rw [hs, Real.sign_of_pos h]; norm_num
  set Dt : ℝ → ℝ := fun t => v0 2 ^ 2 - 2 * γ * c * t with hDt
  have hDpos : ∀ t ∈ Set.Ico 0 (breakdownTime γ v0), 0 < Dt t := by
    intro t ht
    have h2 : t < v0 2 ^ 2 / (2 * γ * c) := ht.2
    rw [lt_div_iff₀ (by positivity)] at h2
    simp only [hDt]; nlinarith
  -- components of M v
  have hmv : ∀ (ω : Fin 3 → ℝ) (t : ℝ),
      (blochMatrix γ ω).mulVec (trackedBloch γ v0 t) =
        ![-γ * v0 0 - ω 0 * v0 1 - ω 2 * (s * √(Dt t)),
          ω 0 * v0 0 - γ * v0 1 - ω 1 * (s * √(Dt t)),
          ω 2 * v0 0 + ω 1 * v0 1] := by
    intro ω t
    funext i
    fin_cases i <;>
      simp [blochMatrix, trackedBloch, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hDt, hs,
        hcdef] <;> ring
  -- derivative of the tracked Bloch vector
  have hderiv : ∀ t ∈ Set.Ico 0 (breakdownTime γ v0), HasDerivAt (trackedBloch γ v0)
      ![0, 0, s * ((-(2 * γ * c)) / (2 * √(Dt t)))] t := by
    intro t ht
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · show HasDerivAt (fun x => trackedBloch γ v0 x 0) (0 : ℝ) t
      exact hasDerivAt_const t (v0 0)
    · show HasDerivAt (fun x => trackedBloch γ v0 x 1) (0 : ℝ) t
      exact hasDerivAt_const t (v0 1)
    · have hD : HasDerivAt Dt (-(2 * γ * c)) t :=
        (((hasDerivAt_id t).const_mul (2 * γ * c)).const_sub (v0 2 ^ 2)).congr_deriv (by ring)
      have h2 := (hD.sqrt (hDpos t ht).ne').const_mul s
      show HasDerivAt (fun x => trackedBloch γ v0 x 2) (s * ((-(2 * γ * c)) / (2 * √(Dt t)))) t
      exact h2
  refine ⟨?_, ?_, ?_⟩
  · funext i
    fin_cases i
    · rfl
    · rfl
    · show s * √(v0 2 ^ 2 - 2 * γ * c * 0) = v0 2
      rw [mul_zero, sub_zero, Real.sqrt_sq_eq_abs, hs]
      rcases lt_or_gt_of_ne hz with h | h
      · rw [Real.sign_of_neg h, abs_of_neg h]; ring
      · rw [Real.sign_of_pos h, abs_of_pos h]; ring
  · intro ω0 t ht
    have hs2' : s ^ 2 = 1 := by rw [sq]; exact hs2
    have hsq : 0 < √(Dt t) := Real.sqrt_pos.mpr (hDpos t ht)
    have hsqsq : √(Dt t) * √(Dt t) = Dt t := Real.mul_self_sqrt (hDpos t ht).le
    have tf0 : trackingFields γ v0 ω0 t 0 = ω0 t := rfl
    have tf1 : trackingFields γ v0 ω0 t 1 = s * (-γ * v0 1 + ω0 t * v0 0) / √(Dt t) := rfl
    have tf2 : trackingFields γ v0 ω0 t 2 = s * (-γ * v0 0 - ω0 t * v0 1) / √(Dt t) := rfl
    have hA : -γ * v0 0 - trackingFields γ v0 ω0 t 0 * v0 1 -
        trackingFields γ v0 ω0 t 2 * (s * √(Dt t)) = 0 := by
      rw [tf0, tf2]; field_simp; rw [hs2']; ring
    have hB : trackingFields γ v0 ω0 t 0 * v0 0 - γ * v0 1 -
        trackingFields γ v0 ω0 t 1 * (s * √(Dt t)) = 0 := by
      rw [tf0, tf1]; field_simp; rw [hs2']; ring
    have hC : trackingFields γ v0 ω0 t 2 * v0 0 + trackingFields γ v0 ω0 t 1 * v0 1 =
        s * ((-(2 * γ * c)) / (2 * √(Dt t))) := by
      rw [tf1, tf2]; field_simp; simp only [hcdef, initCoherence]; ring
    rw [hmv, hA, hB, hC]
    exact hderiv t ht
  · intro ω t ht h
    have hsq : 0 < √(Dt t) := Real.sqrt_pos.mpr (hDpos t ht)
    have hu := h.unique (hderiv t ht)
    rw [hmv] at hu
    have h0 := congrFun hu 0
    have h1 := congrFun hu 1
    simp at h0 h1
    simp only [trackingFields]
    have hz' : s * √(Dt t) ≠ 0 := by
      have : s ≠ 0 := by intro h; rw [h] at hs2; norm_num at hs2
      exact mul_ne_zero this hsq.ne'
    constructor
    · show ω t 1 = Real.sign (v0 2) * (-γ * v0 1 + ω t 0 * v0 0) / √(v0 2 ^ 2 - 2 * γ * c * t)
      change ω t 1 = s * (-γ * v0 1 + ω t 0 * v0 0) / √(Dt t)
      rw [eq_div_iff hsq.ne']
      have : ω t 1 * (s * √(Dt t)) = ω t 0 * v0 0 - γ * v0 1 := by linarith
      have e : ω t 1 * √(Dt t) = s * (ω t 1 * (s * √(Dt t))) := by
        linear_combination (-(ω t 1 * √(Dt t))) * hs2
      rw [e, this]; ring
    · change ω t 2 = s * (-γ * v0 0 - ω t 0 * v0 1) / √(Dt t)
      rw [eq_div_iff hsq.ne']
      have : ω t 2 * (s * √(Dt t)) = -γ * v0 0 - ω t 0 * v0 1 := by linarith
      have e : ω t 2 * √(Dt t) = s * (ω t 2 * (s * √(Dt t))) := by
        linear_combination (-(ω t 2 * √(Dt t))) * hs2
      rw [e, this]
