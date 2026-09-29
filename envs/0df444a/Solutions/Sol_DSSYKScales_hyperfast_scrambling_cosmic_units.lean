-- Prove2me | solution 1 for DSSYKScales.hyperfast_scrambling_cosmic_units
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:13:37.307677+00:00
-- url     : https://prove2.me/submissions/bce80d2c-4f13-47da-a11a-069bede46e7e

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales

theorem aux_hfs_log_div :
    Tendsto (fun x : ℝ => Real.log x / (x - 1)) atTop (𝓝 0) := by
  have := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
  simpa [sub_eq_add_neg] using this

end DSSYKScales

open DSSYKScales
open Filter Topology

theorem solution (N q : ℕ → ℕ) (lam J : ℝ) (hJ : 0 < J)
    (hlim : IsDoubleScaledLimit N q lam) (tc : ℝ) (htc : 0 < tc) :
    Tendsto (fun n => 1 - scramblingProbability (N n) (q n) J tc)
      atTop (𝓝 (Real.exp (-(J * tc)))) := by
  obtain ⟨hlam, hN, hratio⟩ := hlim
  -- q^2 → ∞
  have hq2 : Tendsto (fun n => (q n : ℝ) ^ 2) atTop atTop := by
    have h := hratio.pos_mul_atTop hlam hN
    refine h.congr' ?_
    filter_upwards [hN.eventually_gt_atTop 0] with n hn
    field_simp
  have hq : Tendsto (fun n => (q n : ℝ)) atTop atTop := by
    refine (Real.tendsto_sqrt_atTop.comp hq2).congr ?_
    intro n
    simp [Real.sqrt_sq (Nat.cast_nonneg (q n))]
  have hqm1 : Tendsto (fun n => (q n : ℝ) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1) hq
  -- q / N → 0
  have hqN : Tendsto (fun n => (q n : ℝ) / (N n : ℝ)) atTop (𝓝 0) := by
    have h := hratio.mul (tendsto_inv_atTop_zero.comp hq)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [hq.eventually_gt_atTop 0] with n hn
    simp only [Function.comp]
    field_simp
  -- the exponent
  set y : ℕ → ℝ := fun n =>
    Real.log (1 + (q n : ℝ) / (N n : ℝ) * Real.exp (((q n : ℝ) - 1) * J * tc)) /
      ((q n : ℝ) - 1) with hy
  have hlow : Tendsto (fun n => J * tc + (Real.log (lam / 2) / ((q n : ℝ) - 1)
      - Real.log (q n : ℝ) / ((q n : ℝ) - 1))) atTop (𝓝 (J * tc)) := by
    have h1 := hqm1.const_div_atTop (Real.log (lam / 2))
    have h2 := aux_hfs_log_div.comp hq
    have := (h1.sub h2).const_add (J * tc)
    simpa [Function.comp] using this
  have hup : Tendsto (fun n => J * tc + ((q n : ℝ) / (N n : ℝ)) / ((q n : ℝ) - 1))
      atTop (𝓝 (J * tc)) := by
    have := (hqN.div_atTop hqm1).const_add (J * tc)
    simpa using this
  have hevN : ∀ᶠ n in atTop, (0 : ℝ) < (N n : ℝ) := hN.eventually_gt_atTop 0
  have hevq : ∀ᶠ n in atTop, (2 : ℝ) ≤ (q n : ℝ) := hq.eventually_ge_atTop 2
  have hevr : ∀ᶠ n in atTop, lam / 2 < (q n : ℝ) ^ 2 / (N n : ℝ) :=
    hratio.eventually (lt_mem_nhds (half_lt_self hlam))
  have hyT : Tendsto y atTop (𝓝 (J * tc)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
    · filter_upwards [hevN, hevq, hevr] with n hNn hqn hrn
      have hqpos : (0 : ℝ) < (q n : ℝ) := by linarith
      have hq1 : (0 : ℝ) < (q n : ℝ) - 1 := by linarith
      set E := Real.exp (((q n : ℝ) - 1) * J * tc) with hE
      have hEpos : 0 < E := Real.exp_pos _
      have hx : 0 < (q n : ℝ) / (N n : ℝ) * E := by positivity
      -- lam/(2q) ≤ q/N
      have hle1 : lam / 2 / (q n : ℝ) ≤ (q n : ℝ) / (N n : ℝ) := by
        rw [div_le_div_iff₀ hqpos hNn]
        rw [lt_div_iff₀ hNn] at hrn
        nlinarith
      have hlog1 : Real.log (lam / 2) - Real.log (q n : ℝ) ≤
          Real.log ((q n : ℝ) / (N n : ℝ)) := by
        rw [← Real.log_div (by positivity) hqpos.ne']
        exact Real.log_le_log (by positivity) hle1
      have hlog2 : Real.log ((q n : ℝ) / (N n : ℝ) * E) ≤
          Real.log (1 + (q n : ℝ) / (N n : ℝ) * E) :=
        Real.log_le_log hx (by linarith)
      have hlog3 : Real.log ((q n : ℝ) / (N n : ℝ) * E) =
          Real.log ((q n : ℝ) / (N n : ℝ)) + ((q n : ℝ) - 1) * J * tc := by
        rw [Real.log_mul (by positivity) hEpos.ne', hE, Real.log_exp]
      show J * tc + (Real.log (lam / 2) / ((q n : ℝ) - 1)
        - Real.log (q n : ℝ) / ((q n : ℝ) - 1)) ≤
        Real.log (1 + (q n : ℝ) / (N n : ℝ) * E) / ((q n : ℝ) - 1)
      rw [le_div_iff₀ hq1]
      have heq : (J * tc + (Real.log (lam / 2) / ((q n : ℝ) - 1)
          - Real.log (q n : ℝ) / ((q n : ℝ) - 1))) * ((q n : ℝ) - 1) =
          ((q n : ℝ) - 1) * J * tc + (Real.log (lam / 2) - Real.log (q n : ℝ)) := by
        field_simp
      rw [heq]
      linarith
    · filter_upwards [hevN, hevq] with n hNn hqn
      have hqpos : (0 : ℝ) < (q n : ℝ) := by linarith
      have hq1 : (0 : ℝ) < (q n : ℝ) - 1 := by linarith
      set E := Real.exp (((q n : ℝ) - 1) * J * tc) with hE
      have hEpos : 0 < E := Real.exp_pos _
      have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
      have hu : 0 ≤ (q n : ℝ) / (N n : ℝ) := by positivity
      have hx : 0 < 1 + (q n : ℝ) / (N n : ℝ) * E := by positivity
      have hle : 1 + (q n : ℝ) / (N n : ℝ) * E ≤ (1 + (q n : ℝ) / (N n : ℝ)) * E := by
        nlinarith
      have hlog1 : Real.log (1 + (q n : ℝ) / (N n : ℝ) * E) ≤
          Real.log ((1 + (q n : ℝ) / (N n : ℝ)) * E) := Real.log_le_log hx hle
      have hlog2 : Real.log ((1 + (q n : ℝ) / (N n : ℝ)) * E) =
          Real.log (1 + (q n : ℝ) / (N n : ℝ)) + ((q n : ℝ) - 1) * J * tc := by
        rw [Real.log_mul (by positivity) hEpos.ne', hE, Real.log_exp]
      have hlog3 : Real.log (1 + (q n : ℝ) / (N n : ℝ)) ≤ (q n : ℝ) / (N n : ℝ) := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (q n : ℝ) / (N n : ℝ) by
          positivity)
        linarith
      show Real.log (1 + (q n : ℝ) / (N n : ℝ) * E) / ((q n : ℝ) - 1) ≤
        J * tc + ((q n : ℝ) / (N n : ℝ)) / ((q n : ℝ) - 1)
      rw [div_le_iff₀ hq1]
      have heq : (J * tc + ((q n : ℝ) / (N n : ℝ)) / ((q n : ℝ) - 1)) * ((q n : ℝ) - 1) =
          ((q n : ℝ) - 1) * J * tc + (q n : ℝ) / (N n : ℝ) := by
        field_simp
      rw [heq]
      linarith
  -- conclude
  have hfin : Tendsto (fun n => Real.exp (-(y n))) atTop (𝓝 (Real.exp (-(J * tc)))) :=
    (Real.continuous_exp.tendsto _).comp hyT.neg
  refine hfin.congr' ?_
  filter_upwards [hevN, hevq] with n hNn hqn
  have hx : 0 < 1 + (q n : ℝ) / (N n : ℝ) * Real.exp (((q n : ℝ) - 1) * J * tc) := by
    positivity
  unfold scramblingProbability
  rw [sub_sub_cancel, Real.rpow_def_of_pos hx, hy]
  congr 1
  ring
