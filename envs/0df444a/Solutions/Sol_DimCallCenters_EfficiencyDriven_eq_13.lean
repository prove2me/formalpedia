-- Prove2me | solution 1 for DimCallCenters.EfficiencyDriven.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:27:03.417295+00:00
-- url     : https://prove2.me/submissions/6b197e66-af12-45a1-a3a5-467de76e91ca

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Flam

set_option autoImplicit false

theorem fa74c30a_key (μ : ℝ) (F : ℝ → ℝ) (a b c lam : ℝ)
    (hμ : 0 < μ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F)
    (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b) (hc : 1 < c) (hab : c ≤ a / b) :
    c ≤ DimCallCenters.Rationalized.Flam F μ lam a /
      DimCallCenters.Rationalized.Flam F μ lam b := by
  unfold DimCallCenters.Rationalized.Flam DimCallCenters.Rationalized.servers
  set ν := lam / μ with hν
  have hν0 : 0 < ν := div_pos hlam hμ
  set s := Real.sqrt ν with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hν0
  have hcb : c * b ≤ a := (le_div_iff₀ hb).mp hab
  have hba : b < a := by nlinarith
  have hbs : 0 < b * s := mul_pos hb hs0
  have has : 0 < a * s := mul_pos ha hs0
  have hxs : b * s ≤ a * s := by nlinarith
  have hmem0 : ν ∈ Set.Ioi (0:ℝ) := hν0
  have hmemx : ν + b * s ∈ Set.Ioi (0:ℝ) := by show (0:ℝ) < _; linarith
  have hmemy : ν + a * s ∈ Set.Ioi (0:ℝ) := by show (0:ℝ) < _; linarith
  have hsec := hFconv.secant_mono hmem0 hmemx hmemy (by linarith) (by linarith) (by linarith)
  have hB : 0 < F (ν + b * s) - F ν := sub_pos.mpr (hFmono hmem0 hmemx (by linarith))
  simp only [add_sub_cancel_left] at hsec
  rw [div_le_div_iff₀ hbs has] at hsec
  rw [le_div_iff₀ hB]
  -- hsec : (F x - F ν) * (a*s) ≤ (F y - F ν) * (b*s)
  have h1 : (F (ν + b * s) - F ν) * a ≤ (F (ν + a * s) - F ν) * b := by
    have : ((F (ν + b * s) - F ν) * a) * s ≤ ((F (ν + a * s) - F ν) * b) * s := by
      linarith [hsec]
    exact le_of_mul_le_mul_right this hs0
  nlinarith

open Filter in
theorem solution (μ : ℝ) (F : ℝ → ℝ) (a b : ℝ → ℝ)
    (hμ : 0 < μ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F)
    (hFmono : StrictMonoOn F (Set.Ioi 0))
    (ha : ∀ lam, 0 < lam → 0 < a lam)
    (hb : ∀ lam, 0 < lam → 0 < b lam)
    (hsep : ∃ c : ℝ, 1 < c ∧ ∃ᶠ lam in atTop, c ≤ a lam / b lam) :
    ∃ c : ℝ, 1 < c ∧
      ∃ᶠ lam in atTop,
        c ≤ DimCallCenters.Rationalized.Flam F μ lam (a lam) / DimCallCenters.Rationalized.Flam F μ lam (b lam) := by
  obtain ⟨c, hc, hfr⟩ := hsep
  refine ⟨c, hc, ?_⟩
  refine (hfr.and_eventually (eventually_gt_atTop (0:ℝ))).mono ?_
  rintro lam ⟨hle, hlam⟩
  exact fa74c30a_key μ F (a lam) (b lam) c lam hμ hFconv hFmono hlam (ha lam hlam) (hb lam hlam) hc hle
