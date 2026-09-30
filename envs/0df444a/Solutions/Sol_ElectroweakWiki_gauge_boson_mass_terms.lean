-- Prove2me | solution 1 for ElectroweakWiki.gauge_boson_mass_terms
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:51:26.950951+00:00
-- url     : https://prove2.me/submissions/c91383db-77fb-46fe-a688-f4aa1ca21ef6

import Definitions.Def_ElectroweakWiki_defs
set_option autoImplicit false
open ElectroweakWiki Matrix

theorem higgs_minimum (lam v : ℝ) (hlam : 0 < lam) :
    doubletNormSq (higgsVacuum v) = v ^ 2 / 2 ∧
      higgsPotential lam v (higgsVacuum v) = 0 ∧
      (∀ h : Fin 2 → ℂ, higgsPotential lam v (higgsVacuum v) ≤ higgsPotential lam v h) ∧
      (∀ h : Fin 2 → ℂ, higgsPotential lam v h = 0 ↔ doubletNormSq h = v ^ 2 / 2) := by
  have hn : doubletNormSq (higgsVacuum v) = v ^ 2 / 2 := by
    simp [doubletNormSq, higgsVacuum, Complex.normSq_ofReal, div_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    <;> ring
  have hp : higgsPotential lam v (higgsVacuum v) = 0 := by simp [higgsPotential, hn]
  refine ⟨hn, hp, ?_, ?_⟩
  · intro h
    rw [hp]
    unfold higgsPotential
    positivity
  · intro h
    simp [higgsPotential, mul_eq_zero, hlam.ne', sq_eq_zero_iff, sub_eq_zero]

theorem charge_unbroken (v : ℝ) (hv : v ≠ 0) :
    isospinHyperchargeGenerator 1 1 *ᵥ higgsVacuum v = 0 ∧
      electricCharge (-1 / 2) 1 = 0 ∧
      (∀ a b : ℝ, isospinHyperchargeGenerator a b *ᵥ higgsVacuum v = 0 ↔ a = b) := by
  have hg (a b : ℝ) : isospinHyperchargeGenerator a b *ᵥ higgsVacuum v =
      ![0, (((b-a)*v/(2*Real.sqrt 2) : ℝ) : ℂ)] := by
    ext i
    fin_cases i <;>
      simp [isospinHyperchargeGenerator, higgsVacuum, pauli, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two] <;> push_cast <;> ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hg]
    simp
  · norm_num [electricCharge]
  · intro a b
    constructor
    · intro h
      rw [hg] at h
      have h1 := congrArg (fun f : Fin 2 → ℂ => f 1) h
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at h1
      have hz : (b-a)*v/(2*Real.sqrt 2) = 0 := by exact_mod_cast h1
      have hden : 2 * Real.sqrt 2 ≠ 0 := by positivity
      have hz' : (b-a)*v = 0 := (div_eq_zero_iff.mp hz).resolve_right hden
      have hab := (mul_eq_zero.mp hz').resolve_right hv
      linarith
    · intro h
      rw [hg, h]
      simp

private theorem weinberg_trig (g g' : ℝ) (hg : 0 < g) :
    Real.cos (weinbergAngle g g') = g / Real.sqrt (g^2+g'^2) ∧
    Real.sin (weinbergAngle g g') = g' / Real.sqrt (g^2+g'^2) := by
  have hp : 0 < g^2+g'^2 := by positivity
  have hq : 0 < 1+(g'/g)^2 := by positivity
  have hr := Real.sq_sqrt hp.le
  have hs := Real.sq_sqrt hq.le
  have hsq : (Real.sqrt (1+(g'/g)^2)*g)^2 = (Real.sqrt (g^2+g'^2))^2 := by
    rw [mul_pow, hs, hr]
    field_simp
  have hmul : Real.sqrt (1+(g'/g)^2)*g = Real.sqrt (g^2+g'^2) := by
    have hpos : 0 < Real.sqrt (1+(g'/g)^2)*g := mul_pos (Real.sqrt_pos.mpr hq) hg
    nlinarith [Real.sqrt_pos.mpr hp]
  unfold weinbergAngle
  rw [Real.cos_arctan, Real.sin_arctan, ← hmul]
  constructor <;> field_simp

theorem neutral_current (g g' T3 Y B W3 : ℝ) (hg : 0 < g) (hg' : 0 < g') :
    g * T3 * W3 + g' * (Y / 2) * B =
      elemCharge g g' * electricCharge T3 Y * photonField (weinbergAngle g g') B W3 +
        g / Real.cos (weinbergAngle g g') *
          (T3 - Real.sin (weinbergAngle g g') ^ 2 * electricCharge T3 Y) *
            zField (weinbergAngle g g') B W3 := by
  obtain ⟨hc, hs⟩ := weinberg_trig g g' hg
  have hp : 0 < g^2+g'^2 := by positivity
  have hn := (Real.sqrt_pos.mpr hp).ne'
  have hsq := Real.sq_sqrt hp.le
  unfold elemCharge electricCharge photonField zField
  rw [hc, hs]
  field_simp [hg.ne', hn]
  simp only [hsq]
  ring

theorem solution (g g' v W1 W2 W3 B : ℝ) (hg : 0 < g) (hg' : 0 < g') :
    (doubletNormSq (gaugeTerm g g' 1 B W1 W2 W3 *ᵥ higgsVacuum v) : ℂ) =
      (wMass g v : ℂ) ^ 2 * wPlus W1 W2 * wMinus W1 W2 +
        1 / 2 * (zMass g g' v : ℂ) ^ 2 * (zField (weinbergAngle g g') B W3 : ℂ) ^ 2 := by
  obtain ⟨hc, hs⟩ := weinberg_trig g g' hg
  have hp : 0 < g^2+g'^2 := by positivity
  have hn := (Real.sqrt_pos.mpr hp).ne'
  have hsq := Real.sq_sqrt hp.le
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn2 : Real.sqrt 2 ≠ 0 := by positivity
  unfold doubletNormSq gaugeTerm higgsVacuum wMass wPlus wMinus zMass zField
  rw [hc, hs]
  apply Complex.ext
  all_goals simp [pauli, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.normSq_apply]
  all_goals simp [pow_two, Complex.mul_re, Complex.mul_im]
  all_goals field_simp [hn, hn2]
  all_goals simp only [hs2, hsq]
  all_goals ring
