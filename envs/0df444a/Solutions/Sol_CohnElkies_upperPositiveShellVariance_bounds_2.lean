-- Prove2me | solution 2 for CohnElkies.upperPositiveShellVariance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:44:00.603571+00:00
-- url     : https://prove2.me/submissions/84fe80f0-9b86-4f20-809c-a6cf82107786

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    (1 / 2 : ℝ) * (shellLocation ε) ^ 2 *
        shellWeight ε *
          Real.exp (δ * shellLocation ε) ≤
      upperPositiveShellVariance ε δ ∧
    upperPositiveShellVariance ε δ ≤
      (shellLocation ε + 1) ^ 2 *
        shellWeight ε *
          Real.exp (δ * (shellLocation ε + 1)) := by
  unfold upperPositiveShellVariance positiveShellDensity
  have hs : 0 < shellLocation ε := by unfold shellLocation; positivity
  have hW := shellWeight_pos ε
  have hcont : Continuous (fun a : ℝ => shellWeight ε / Real.cosh a * a ^ 2 * Real.cosh ((1 + δ) * a)) :=
    ((continuous_const.div Real.continuous_cosh fun a => (Real.cosh_pos a).ne').mul
      (continuous_pow 2)).mul (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
  have hint := hcont.intervalIntegrable (μ := MeasureTheory.volume) (shellLocation ε) (shellLocation ε + 1)
  have hle1 : shellLocation ε ≤ shellLocation ε + 1 := by linarith
  constructor
  · have hle : ∀ a ∈ Set.Icc (shellLocation ε) (shellLocation ε + 1),
        (1 / 2 : ℝ) * (shellLocation ε) ^ 2 * shellWeight ε * Real.exp (δ * shellLocation ε) ≤
          shellWeight ε / Real.cosh a * a ^ 2 * Real.cosh ((1 + δ) * a) := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := ha
      have ha0 : 0 < a := by linarith
      rw [show shellWeight ε / Real.cosh a * a ^ 2 * Real.cosh ((1 + δ) * a) =
          shellWeight ε * a ^ 2 * Real.cosh ((1 + δ) * a) / Real.cosh a by ring,
        le_div_iff₀ (Real.cosh_pos a)]
      have h1 : Real.cosh a ≤ Real.exp a := by
        rw [Real.cosh_eq]
        have : Real.exp (-a) ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
        linarith
      have h2 : Real.exp ((1 + δ) * a) / 2 ≤ Real.cosh ((1 + δ) * a) := by
        rw [Real.cosh_eq]; have := Real.exp_pos (-((1 + δ) * a)); linarith
      have h3 : Real.exp (δ * shellLocation ε) * Real.exp a ≤ Real.exp ((1 + δ) * a) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
      have h4 : (shellLocation ε) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hs.le ha1 2
      have he := Real.exp_pos (δ * shellLocation ε)
      calc (1 / 2 : ℝ) * (shellLocation ε) ^ 2 * shellWeight ε * Real.exp (δ * shellLocation ε) * Real.cosh a
          ≤ (1 / 2 : ℝ) * (shellLocation ε) ^ 2 * shellWeight ε * Real.exp (δ * shellLocation ε) * Real.exp a :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (1 / 2 : ℝ) * ((shellLocation ε) ^ 2 * shellWeight ε) *
              (Real.exp (δ * shellLocation ε) * Real.exp a) := by ring
        _ ≤ (1 / 2 : ℝ) * (a ^ 2 * shellWeight ε) * Real.exp ((1 + δ) * a) := by
            apply mul_le_mul _ h3 (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hW.le) (by norm_num)
        _ ≤ shellWeight ε * a ^ 2 * Real.cosh ((1 + δ) * a) := by
            have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ shellWeight ε * a ^ 2)
            nlinarith
    calc (1 / 2 : ℝ) * (shellLocation ε) ^ 2 * shellWeight ε * Real.exp (δ * shellLocation ε)
        = ∫ a in shellLocation ε..shellLocation ε + 1,
            (1 / 2 : ℝ) * (shellLocation ε) ^ 2 * shellWeight ε * Real.exp (δ * shellLocation ε) := by
          simp
      _ ≤ _ := intervalIntegral.integral_mono_on hle1 intervalIntegrable_const hint hle
  · have hle : ∀ a ∈ Set.Icc (shellLocation ε) (shellLocation ε + 1),
        shellWeight ε / Real.cosh a * a ^ 2 * Real.cosh ((1 + δ) * a) ≤
          (shellLocation ε + 1) ^ 2 * shellWeight ε * Real.exp (δ * (shellLocation ε + 1)) := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := ha
      have ha0 : 0 < a := by linarith
      rw [show shellWeight ε / Real.cosh a * a ^ 2 * Real.cosh ((1 + δ) * a) =
          shellWeight ε * a ^ 2 * Real.cosh ((1 + δ) * a) / Real.cosh a by ring,
        div_le_iff₀ (Real.cosh_pos a)]
      have h5 : Real.cosh ((1 + δ) * a) ≤ Real.exp (δ * a) * Real.cosh a := by
        rw [Real.cosh_eq, Real.cosh_eq]
        have e1 : Real.exp ((1 + δ) * a) = Real.exp (δ * a) * Real.exp a := by
          rw [← Real.exp_add]; ring_nf
        have e2 : Real.exp (-((1 + δ) * a)) ≤ Real.exp (δ * a) * Real.exp (-a) := by
          rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
        rw [e1]; nlinarith
      have h6 : a ^ 2 ≤ (shellLocation ε + 1) ^ 2 := pow_le_pow_left₀ ha0.le ha2 2
      have h7 : Real.exp (δ * a) ≤ Real.exp (δ * (shellLocation ε + 1)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha2 hδ)
      have h8 : a ^ 2 * Real.exp (δ * a) ≤ (shellLocation ε + 1) ^ 2 * Real.exp (δ * (shellLocation ε + 1)) :=
        mul_le_mul h6 h7 (Real.exp_pos _).le (by positivity)
      calc shellWeight ε * a ^ 2 * Real.cosh ((1 + δ) * a)
          ≤ shellWeight ε * a ^ 2 * (Real.exp (δ * a) * Real.cosh a) :=
            mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = shellWeight ε * (a ^ 2 * Real.exp (δ * a)) * Real.cosh a := by ring
        _ ≤ shellWeight ε * ((shellLocation ε + 1) ^ 2 * Real.exp (δ * (shellLocation ε + 1))) * Real.cosh a := by
            apply mul_le_mul_of_nonneg_right _ (Real.cosh_pos a).le
            exact mul_le_mul_of_nonneg_left h8 hW.le
        _ = (shellLocation ε + 1) ^ 2 * shellWeight ε * Real.exp (δ * (shellLocation ε + 1)) * Real.cosh a := by ring
    calc _ ≤ ∫ a in shellLocation ε..shellLocation ε + 1,
            (shellLocation ε + 1) ^ 2 * shellWeight ε * Real.exp (δ * (shellLocation ε + 1)) :=
          intervalIntegral.integral_mono_on hle1 hint intervalIntegrable_const hle
      _ = _ := by simp

