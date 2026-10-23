-- Prove2me | solution 1 for FoodDeliv.Decentral.lemma_C_6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:44:26.1239+00:00
-- url     : https://prove2.me/submissions/43e4c3c0-988d-4aa4-8819-ddd766af2b72

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

open FoodDeliv.Decentral

theorem g78f_deriv (R μ c x : ℝ) (hx : x < R) :
    HasDerivAt (fun p => p * (μ - c / (R - p))) (μ - c * R / (R - x) ^ 2) x := by
  have h1 : HasDerivAt (fun p : ℝ => R - p) (-1) x := (hasDerivAt_id' x).const_sub R
  have hne : R - x ≠ 0 := by linarith
  have h2 := (hasDerivAt_const x c).div h1 hne
  have h3 := (hasDerivAt_id' x).mul ((hasDerivAt_const x μ).sub h2)
  refine h3.congr_deriv ?_
  simp only [Pi.sub_apply, Pi.div_apply]
  field_simp
  ring

theorem solution (R μ c ϕ : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hϕ : 0 < ϕ) (hϕc : ϕ < c) :
    (R - c / μ) * (μ - c / (R - (R - c / μ))) = 0 ∧
    (∃ m ∈ Set.Ioc 0 (R - ϕ / μ),
      StrictMonoOn (fun p => p * (μ - c / (R - p))) (Set.Ioc 0 m) ∧
      StrictAntiOn (fun p => p * (μ - c / (R - p))) (Set.Icc m (R - ϕ / μ))) ∧
    IsGreatest ((fun p => p * (μ - c / (R - p))) '' Set.Ioc 0 (R - ϕ / μ))
      ((Real.sqrt (R * μ) - Real.sqrt c) ^ 2) ∧
    {p ∈ Set.Ioc 0 (R - ϕ / μ) | ∀ q ∈ Set.Ioc 0 (R - ϕ / μ),
        q * (μ - c / (R - q)) ≤ p * (μ - c / (R - p))} =
      {R - Real.sqrt (c / μ * R)} ∧
    (R - Real.sqrt (c / μ * R) ≤ R - c ^ 2 / (μ * ϕ) ↔ ϕ ≥ Real.sqrt (c ^ 3 / (R * μ))) ∧
    (R - Real.sqrt (c / μ * R) ≥ R - c ^ 2 / (μ * ϕ) ↔ ϕ ≤ Real.sqrt (c ^ 3 / (R * μ))) := by
  have hR : 0 < R := by
    by_contra h; push_neg at h; nlinarith
  set f : ℝ → ℝ := fun p => p * (μ - c / (R - p)) with hf
  set s := Real.sqrt (c / μ * R) with hs
  have hs2 : s ^ 2 = c / μ * R := Real.sq_sqrt (by positivity)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hsR : s < R := by
    have : s ^ 2 < R ^ 2 := by
      rw [hs2, div_mul_eq_mul_div, div_lt_iff₀ hμ]; nlinarith
    nlinarith
  have hϕs : ϕ / μ ≤ s := by
    have : (ϕ / μ) ^ 2 ≤ s ^ 2 := by
      rw [hs2, div_pow, div_le_iff₀ (by positivity)]
      have : ϕ ^ 2 ≤ c * (R * μ) := by nlinarith
      calc ϕ ^ 2 ≤ c * (R * μ) := this
        _ = c / μ * R * μ ^ 2 := by field_simp
    nlinarith [div_pos hϕ hμ]
  set m := R - s with hm
  have hm0 : 0 < m := by linarith
  have hmD : m ≤ R - ϕ / μ := by linarith
  have hD : ∀ p, p ≤ R - ϕ / μ → p < R := fun p hp => by
    have : 0 < ϕ / μ := div_pos hϕ hμ; linarith
  have hcont : ∀ t : Set ℝ, (∀ p ∈ t, p < R) → ContinuousOn f t := fun t ht p hp =>
    (g78f_deriv R μ c p (ht p hp)).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Set.Ioc 0 m) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioc 0 m) (hcont _ fun p hp => by linarith [hp.2])
      fun x hx => ?_
    rw [interior_Ioc] at hx
    rw [(g78f_deriv R μ c x (by linarith [hx.2])).deriv]
    have h1 : s < R - x := by linarith [hx.2]
    have h2 : s ^ 2 < (R - x) ^ 2 := by nlinarith
    have h3 : c * R < μ * (R - x) ^ 2 := by
      rw [hs2] at h2
      have := (div_mul_eq_mul_div c μ R) ▸ h2
      rw [div_lt_iff₀ hμ] at this; linarith
    have h4 : c * R / (R - x) ^ 2 < μ := by
      rw [div_lt_iff₀ (by nlinarith)]; linarith
    linarith
  have hanti : StrictAntiOn f (Set.Icc m (R - ϕ / μ)) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc m (R - ϕ / μ))
      (hcont _ fun p hp => hD p hp.2) fun x hx => ?_
    rw [interior_Icc] at hx
    have hxR : x < R := hD x hx.2.le
    rw [(g78f_deriv R μ c x hxR).deriv]
    have h1 : R - x < s := by linarith [hx.1]
    have h0 : 0 < R - x := by linarith
    have h2 : (R - x) ^ 2 < s ^ 2 := by nlinarith
    have h3 : μ * (R - x) ^ 2 < c * R := by
      rw [hs2] at h2
      have := (div_mul_eq_mul_div c μ R) ▸ h2
      rw [lt_div_iff₀ hμ] at this; linarith
    have h4 : μ < c * R / (R - x) ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  -- value at the maximizer
  set a := Real.sqrt (R * μ) with ha
  set b := Real.sqrt c with hb
  have ha2 : a ^ 2 = R * μ := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = c := Real.sq_sqrt hc.le
  have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hb0 : 0 < b := Real.sqrt_pos.2 hc
  have hsab : s = b * a / μ := by
    rw [hs]
    have : c / μ * R = (b * a / μ) ^ 2 := by
      rw [div_pow, mul_pow, ha2, hb2]; field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  have hfm : f m = (a - b) ^ 2 := by
    simp only [hf, hm, sub_sub_cancel, hsab]
    have hRa : R = a ^ 2 / μ := by rw [ha2]; field_simp
    have hcb : c = b ^ 2 := hb2.symm
    rw [hRa, hcb]
    field_simp
  have hle : ∀ p ∈ Set.Ioc 0 (R - ϕ / μ), f p ≤ f m := by
    intro p hp
    rcases le_total p m with h | h
    · exact hmono.monotoneOn ⟨hp.1, h⟩ ⟨hm0, le_rfl⟩ h
    · exact hanti.antitoneOn ⟨le_rfl, hmD⟩ ⟨h, hp.2⟩ h
  refine ⟨?_, ⟨m, ⟨hm0, hmD⟩, hmono, hanti⟩, ⟨⟨m, ⟨hm0, hmD⟩, hfm⟩, ?_⟩, ?_, ?_, ?_⟩
  · have : R - (R - c / μ) = c / μ := by ring
    have h2 : c / (c / μ) = μ := by field_simp
    rw [this, h2, sub_self, mul_zero]
  · rintro _ ⟨p, hp, rfl⟩
    rw [← hfm]; exact hle p hp
  · ext p
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp, hmax⟩
      have h1 := hmax m ⟨hm0, hmD⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := hmono ⟨hp.1, h.le⟩ ⟨hm0, le_rfl⟩ h
        exact absurd h1 (not_le.2 this)
      · have := hanti ⟨le_rfl, hmD⟩ ⟨h.le, hp.2⟩ h
        exact absurd h1 (not_le.2 this)
    · rintro rfl
      exact ⟨⟨hm0, hmD⟩, fun q hq => hle q hq⟩
  · have E1 : c ^ 2 / (μ * ϕ) ≤ s ↔ c ^ 3 ≤ R * μ * ϕ ^ 2 := by
      rw [← pow_le_pow_iff_left₀ (by positivity) hs0.le two_ne_zero, hs2, div_pow, mul_pow,
        div_le_iff₀ (by positivity)]
      have : c / μ * R * (μ ^ 2 * ϕ ^ 2) = c * (R * μ * ϕ ^ 2) := by field_simp
      rw [this, show (c ^ 2) ^ 2 = c * c ^ 3 by ring]
      exact mul_le_mul_iff_of_pos_left hc
    have E2 : Real.sqrt (c ^ 3 / (R * μ)) ≤ ϕ ↔ c ^ 3 ≤ R * μ * ϕ ^ 2 := by
      have hϕs : ϕ = Real.sqrt (ϕ ^ 2) := (Real.sqrt_sq hϕ.le).symm
      constructor
      · intro h
        rw [hϕs, Real.sqrt_le_sqrt_iff (sq_nonneg ϕ), div_le_iff₀ (by positivity)] at h
        linarith
      · intro h
        rw [hϕs]
        exact Real.sqrt_le_sqrt (by rw [div_le_iff₀ (by positivity)]; linarith)
    rw [ge_iff_le, E2, ← E1]
    constructor <;> intro h <;> linarith
  · have E1 : s ≤ c ^ 2 / (μ * ϕ) ↔ R * μ * ϕ ^ 2 ≤ c ^ 3 := by
      rw [← pow_le_pow_iff_left₀ hs0.le (by positivity) two_ne_zero, hs2, div_pow, mul_pow,
        le_div_iff₀ (by positivity)]
      have : c / μ * R * (μ ^ 2 * ϕ ^ 2) = c * (R * μ * ϕ ^ 2) := by field_simp
      rw [this, show (c ^ 2) ^ 2 = c * c ^ 3 by ring]
      exact mul_le_mul_iff_of_pos_left hc
    have E2 : ϕ ≤ Real.sqrt (c ^ 3 / (R * μ)) ↔ R * μ * ϕ ^ 2 ≤ c ^ 3 := by
      have hϕs : ϕ = Real.sqrt (ϕ ^ 2) := (Real.sqrt_sq hϕ.le).symm
      constructor
      · intro h
        rw [hϕs, Real.sqrt_le_sqrt_iff (by positivity), le_div_iff₀ (by positivity)] at h
        linarith
      · intro h
        rw [hϕs]
        exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ (by positivity)]; linarith)
    rw [ge_iff_le, E2, ← E1]
    constructor <;> intro h <;> linarith
