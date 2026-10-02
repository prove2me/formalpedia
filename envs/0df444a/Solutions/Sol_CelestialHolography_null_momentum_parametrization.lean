-- Prove2me | solution 1 for CelestialHolography.null_momentum_parametrization
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T14:14:14.001774+00:00
-- url     : https://prove2.me/submissions/eb3c4c87-36a9-4460-9ac1-b0e0c481f2ce

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

set_option autoImplicit false

open CelestialHolography in
theorem a5f830ad_pos (p : Fin 4 → ℝ) (hnull : minkowskiNormSq p = 0)
    (hfut : 0 < p 0) (hpole : p 0 + p 3 ≠ 0) : 0 < p 0 + p 3 := by
  unfold minkowskiNormSq at hnull
  rcases lt_or_gt_of_ne hpole with h | h
  · exfalso
    nlinarith [sq_nonneg (p 1), sq_nonneg (p 2)]
  · exact h

open CelestialHolography in
theorem a5f830ad_components (w : ℝ) (z : ℂ) :
    (w • nullVector z) 0 = w * ((1 + Complex.normSq z) / Real.sqrt 2) ∧
    (w • nullVector z) 1 = w * (2 * z.re / Real.sqrt 2) ∧
    (w • nullVector z) 2 = w * (2 * z.im / Real.sqrt 2) ∧
    (w • nullVector z) 3 = w * ((1 - Complex.normSq z) / Real.sqrt 2) := by
  simp [nullVector]

open CelestialHolography in
theorem a5f830ad_unique (p : Fin 4 → ℝ) (hpos : 0 < p 0 + p 3)
    (w : ℝ) (z : ℂ) (h : p = w • nullVector z) :
    w = (p 0 + p 3) / Real.sqrt 2 ∧
      z = ⟨p 1 / (p 0 + p 3), p 2 / (p 0 + p 3)⟩ := by
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨h0, h1, h2, h3⟩ := a5f830ad_components w z
  rw [← h] at h0 h1 h2 h3
  have hsum : p 0 + p 3 = w * 2 / Real.sqrt 2 := by
    rw [h0, h3]; field_simp; ring
  have hw : w = (p 0 + p 3) / Real.sqrt 2 := by
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [hsum]; field_simp; simp [hsq]
  have hw0 : w ≠ 0 := by
    intro hw0; rw [hw0] at hsum; simp at hsum; linarith
  refine ⟨hw, ?_⟩
  apply Complex.ext
  · simp only
    rw [hsum, h1]; field_simp
  · simp only
    rw [hsum, h2]; field_simp

open CelestialHolography in
theorem solution (p : Fin 4 → ℝ) (hnull : minkowskiNormSq p = 0)
    (hfut : 0 < p 0) (hpole : p 0 + p 3 ≠ 0) :
    ∃! wz : ℝ × ℂ, 0 < wz.1 ∧ p = wz.1 • nullVector wz.2 := by
  have ha := a5f830ad_pos p hnull hfut hpole
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have ha0 : p 0 + p 3 ≠ 0 := ne_of_gt ha
  unfold minkowskiNormSq at hnull
  refine ⟨((p 0 + p 3) / Real.sqrt 2, ⟨p 1 / (p 0 + p 3), p 2 / (p 0 + p 3)⟩), ⟨by positivity, ?_⟩, ?_⟩
  · funext i
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    fin_cases i <;> simp [nullVector, Complex.normSq_apply] <;> field_simp <;>
      first | nlinarith [hs2] | simp [hsq]
  · rintro ⟨w, z⟩ ⟨_, h⟩
    obtain ⟨hw, hz⟩ := a5f830ad_unique p ha w z h
    rw [hw, hz]
