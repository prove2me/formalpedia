-- Prove2me | solution 1 for CongestedPlatforms.Surge.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T22:49:52.368496+00:00
-- url     : https://prove2.me/submissions/766a6a03-ce22-4ad4-9448-666453d1c472

import Mathlib
import Definitions.Def_CongestedPlatforms_Surge_Setting

namespace CongestedPlatforms.Surge

theorem l1_P (lam γ x p d s : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hx : 0 < x) (hp : p < 1)
    (hd : 0 < d) (hs : 0 < s) :
    (d = lam * (1 - p - γ * (d / s) ^ 2) ∧ s = x * (d / s)) ↔
      (d = lam * x * (1 - p) / (x + lam * γ) ∧
        s = x * Real.sqrt (lam * (1 - p) / (x + lam * γ))) := by
  have hxl : 0 < x + lam * γ := by positivity
  have hQ : 0 < lam * (1 - p) / (x + lam * γ) := by
    apply div_pos (mul_pos hlam (by linarith)) hxl
  have hsq := Real.sq_sqrt hQ.le
  have hsp := Real.sqrt_pos.mpr hQ
  constructor
  · rintro ⟨h1, h2⟩
    set ρ := d / s with hρ
    have hρpos : 0 < ρ := div_pos hd hs
    have hd2 : d = x * ρ ^ 2 := by
      have : d = ρ * s := by rw [hρ]; field_simp
      rw [this, h2]; ring
    have hQe : ρ ^ 2 = lam * (1 - p) / (x + lam * γ) := by
      rw [eq_div_iff hxl.ne']
      rw [hd2] at h1
      nlinarith
    have hρe : ρ = Real.sqrt (lam * (1 - p) / (x + lam * γ)) := by
      rw [← hQe, Real.sqrt_sq hρpos.le]
    refine ⟨?_, ?_⟩
    · rw [hd2, hQe]; field_simp
    · rw [h2, ← hρe]
  · rintro ⟨h1, h2⟩
    set Q := lam * (1 - p) / (x + lam * γ) with hQdef
    set r := Real.sqrt Q with hr
    have hd2 : d = x * Q := by rw [h1, hQdef]; field_simp
    have hρ : d / s = r := by
      rw [h1, h2]
      rw [show lam * x * (1 - p) / (x + lam * γ) = x * Q by rw [hQdef]; field_simp]
      rw [← hsq]; field_simp
    refine ⟨?_, ?_⟩
    · rw [hρ, hsq]
      have : lam * (1 - p) = Q * (x + lam * γ) := by rw [hQdef]; field_simp
      rw [hd2]; nlinarith
    · rw [hρ]; exact h2

theorem l1_F (lam γ x0 x1 e0 e1 d0 s0 d1 s1 : ℝ) (hlam : 0 < lam) (hγ : 0 < γ)
    (hx0 : 0 < x0) (hx1 : 0 < x1) (he : e0 + e1 = 2)
    (hd0 : 0 < d0) (hd1 : 0 < d1) (hs0 : 0 < s0) (hs1 : 0 < s1) :
    (d0 = 1 / 2 * lam * (e0 - γ * ((d0 / s0) ^ 2 - (d1 / s1) ^ 2)) ∧
      d1 = 1 / 2 * lam * (e1 - γ * ((d1 / s1) ^ 2 - (d0 / s0) ^ 2)) ∧
      s0 = x0 * (d0 / s0) ∧ s1 = x1 * (d1 / s1)) ↔
    (d0 = lam * x0 * (lam * γ + x1 * e0) / (2 * x0 * x1 + lam * γ * (x0 + x1)) ∧
     d1 = lam * x1 * (lam * γ + x0 * e1) / (2 * x1 * x0 + lam * γ * (x1 + x0)) ∧
     s0 = x0 * Real.sqrt (lam * (lam * γ + x1 * e0) / (2 * x0 * x1 + lam * γ * (x0 + x1))) ∧
     s1 = x1 * Real.sqrt (lam * (lam * γ + x0 * e1) / (2 * x1 * x0 + lam * γ * (x1 + x0)))) := by
  have hden : 0 < 2 * x0 * x1 + lam * γ * (x0 + x1) := by positivity
  have hden' : 2 * x1 * x0 + lam * γ * (x1 + x0) = 2 * x0 * x1 + lam * γ * (x0 + x1) := by ring
  rw [hden']
  set den := 2 * x0 * x1 + lam * γ * (x0 + x1) with hdendef
  set N0 := lam * γ + x1 * e0 with hN0
  set N1 := lam * γ + x0 * e1 with hN1
  set Q0 := lam * N0 / den with hQ0
  set Q1 := lam * N1 / den with hQ1
  constructor
  · rintro ⟨E0, E1, h0, h1⟩
    have hρ0 : 0 < d0 / s0 := div_pos hd0 hs0
    have hρ1 : 0 < d1 / s1 := div_pos hd1 hs1
    set ρ0 := d0 / s0 with hρ0d
    set ρ1 := d1 / s1 with hρ1d
    have hd0' : d0 = x0 * ρ0 ^ 2 := by
      have : d0 = ρ0 * s0 := by rw [hρ0d]; field_simp
      rw [this, h0]; ring
    have hd1' : d1 = x1 * ρ1 ^ 2 := by
      have : d1 = ρ1 * s1 := by rw [hρ1d]; field_simp
      rw [this, h1]; ring
    rw [hd0'] at E0
    rw [hd1'] at E1
    have hr0 : ρ0 ^ 2 * den = lam * N0 := by
      rw [hdendef, hN0]
      linear_combination (2*x1+lam*γ) * E0 + lam*γ * E1 + (lam*lam*γ/2) * he
    have hr1 : ρ1 ^ 2 * den = lam * N1 := by
      rw [hdendef, hN1]
      linear_combination (2*x0+lam*γ) * E1 + lam*γ * E0 + (lam*lam*γ/2) * he
    have hq0 : ρ0 ^ 2 = Q0 := by rw [hQ0]; field_simp; linarith
    have hq1 : ρ1 ^ 2 = Q1 := by rw [hQ1]; field_simp; linarith
    have hs0' : ρ0 = Real.sqrt Q0 := by rw [← hq0, Real.sqrt_sq hρ0.le]
    have hs1' : ρ1 = Real.sqrt Q1 := by rw [← hq1, Real.sqrt_sq hρ1.le]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hd0', hq0, hQ0]; field_simp
    · rw [hd1', hq1, hQ1]; field_simp
    · rw [h0, ← hs0']
    · rw [h1, ← hs1']
  · rintro ⟨h0, h1, h2, h3⟩
    have hd0e : d0 = x0 * Q0 := by rw [h0, hQ0]; field_simp
    have hd1e : d1 = x1 * Q1 := by rw [h1, hQ1]; field_simp
    have hQ0p : 0 < Q0 := by
      have : 0 < x0 * Q0 := hd0e ▸ hd0
      exact (pos_iff_pos_of_mul_pos this).mp hx0
    have hQ1p : 0 < Q1 := by
      have : 0 < x1 * Q1 := hd1e ▸ hd1
      exact (pos_iff_pos_of_mul_pos this).mp hx1
    have hsq0 := Real.sq_sqrt hQ0p.le
    have hsq1 := Real.sq_sqrt hQ1p.le
    have hsp0 := Real.sqrt_pos.mpr hQ0p
    have hsp1 := Real.sqrt_pos.mpr hQ1p
    have hρ0 : d0 / s0 = Real.sqrt Q0 := by
      rw [hd0e, h2, div_eq_iff (by positivity)]
      linear_combination (-x0) * hsq0
    have hρ1 : d1 / s1 = Real.sqrt Q1 := by
      rw [hd1e, h3, div_eq_iff (by positivity)]
      linear_combination (-x1) * hsq1
    have hr0 : Q0 * den = lam * N0 := by rw [hQ0]; field_simp
    have hr1 : Q1 * den = lam * N1 := by rw [hQ1]; field_simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hρ0, hρ1, hsq0, hsq1, hd0e]
      apply mul_right_cancel₀ hden.ne'
      rw [hdendef] at hr0 hr1 ⊢
      linear_combination (x0 + lam*γ/2) * hr0 - (lam*γ/2) * hr1 + (-(x0*lam^2*γ/2)) * he
    · rw [hρ0, hρ1, hsq0, hsq1, hd1e]
      apply mul_right_cancel₀ hden.ne'
      rw [hdendef] at hr0 hr1 ⊢
      linear_combination (x1 + lam*γ/2) * hr1 - (lam*γ/2) * hr0 + (-(x1*lam^2*γ/2)) * he
    · rw [hρ0]; exact h2
    · rw [hρ1]; exact h3

theorem dP_pos (lam γ α c p : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hx : 0 < α * p - c) (hp : p < 1) :
    0 < dP lam γ α c p := by
  unfold dP
  have : 0 < 1 - p := by linarith
  positivity

theorem sP_pos (lam γ α c p : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hx : 0 < α * p - c) (hp : p < 1) :
    0 < sP lam γ α c p := by
  unfold sP
  have : 0 < 1 - p := by linarith
  have h2 : 0 < lam * (1 - p) / (α * p - c + lam * γ) := by positivity
  have := Real.sqrt_pos.mpr h2
  positivity

theorem dP_eq (lam γ α c p : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hx : 0 < α * p - c) (hp : p < 1) :
    dP lam γ α c p = lam * (1 - p - γ * (dP lam γ α c p / sP lam γ α c p) ^ 2) := by
  have h := (l1_P lam γ (α * p - c) p (dP lam γ α c p) (sP lam γ α c p) hlam hγ hx hp
    (dP_pos lam γ α c p hlam hγ hx hp) (sP_pos lam γ α c p hlam hγ hx hp)).mpr
    ⟨rfl, rfl⟩
  exact h.1

theorem lemma_1_aux (lam γ α c p0 p1 : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hc : 0 ≤ c) (hx0 : 0 < α * p0 - c) (hx1 : 0 < α * p1 - c) (hp0 : p0 < 1) (hp1 : p1 < 1) :
    (∀ d0 d1 s0 s1 : ℝ, 0 < d0 → 0 < d1 → 0 < s0 → 0 < s1 →
      ((d0 = lam * (1 - p0 - γ * (d0 / s0) ^ 2) ∧ d1 = lam * (1 - p1 - γ * (d1 / s1) ^ 2) ∧
          s0 = (α * p0 - c) * (d0 / s0) ∧ s1 = (α * p1 - c) * (d1 / s1)) ↔
        (d0 = dP lam γ α c p0 ∧ d1 = dP lam γ α c p1 ∧
          s0 = sP lam γ α c p0 ∧ s1 = sP lam γ α c p1))) ∧
    (1 - p0 - γ * (dP lam γ α c p0 / sP lam γ α c p0) ^ 2 ≤
        p1 + γ * (dP lam γ α c p1 / sP lam γ α c p1) ^ 2 ↔
      dP lam γ α c p0 + dP lam γ α c p1 ≤ lam) ∧
    (∀ d0 d1 s0 s1 : ℝ, 0 < d0 → 0 < d1 → 0 < s0 → 0 < s1 →
      ((d0 = 1 / 2 * lam * (1 - p0 + p1 - γ * ((d0 / s0) ^ 2 - (d1 / s1) ^ 2)) ∧
          d1 = 1 / 2 * lam * (1 - p1 + p0 - γ * ((d1 / s1) ^ 2 - (d0 / s0) ^ 2)) ∧
          s0 = (α * p0 - c) * (d0 / s0) ∧ s1 = (α * p1 - c) * (d1 / s1)) ↔
        (d0 = dF lam γ α c p0 p1 ∧ d1 = dF lam γ α c p1 p0 ∧
          s0 = sF lam γ α c p0 p1 ∧ s1 = sF lam γ α c p1 p0))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d0 d1 s0 s1 hd0 hd1 hs0 hs1
    have a := l1_P lam γ (α * p0 - c) p0 d0 s0 hlam hγ hx0 hp0 hd0 hs0
    have b := l1_P lam γ (α * p1 - c) p1 d1 s1 hlam hγ hx1 hp1 hd1 hs1
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have a' := a.mp ⟨h1, h3⟩
      have b' := b.mp ⟨h2, h4⟩
      exact ⟨a'.1, b'.1, a'.2, b'.2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      have a' := a.mpr ⟨h1, h3⟩
      have b' := b.mpr ⟨h2, h4⟩
      exact ⟨a'.1, b'.1, a'.2, b'.2⟩
  · have e0 := dP_eq lam γ α c p0 hlam hγ hx0 hp0
    have e1 := dP_eq lam γ α c p1 hlam hγ hx1 hp1
    set ρ0 := dP lam γ α c p0 / sP lam γ α c p0
    set ρ1 := dP lam γ α c p1 / sP lam γ α c p1
    have k0 : 1 - p0 - γ * ρ0 ^ 2 = dP lam γ α c p0 / lam := by
      field_simp; linarith
    have k1 : p1 + γ * ρ1 ^ 2 = 1 - dP lam γ α c p1 / lam := by
      field_simp; linarith
    rw [k0, k1]
    constructor
    · intro h
      have h2 : dP lam γ α c p0 / lam + dP lam γ α c p1 / lam ≤ 1 := by linarith
      rw [← add_div, div_le_one hlam] at h2
      exact h2
    · intro h
      have h2 : (dP lam γ α c p0 + dP lam γ α c p1) / lam ≤ 1 := by
        rw [div_le_one hlam]; exact h
      rw [add_div] at h2
      linarith
  · intro d0 d1 s0 s1 hd0 hd1 hs0 hs1
    have key := l1_F lam γ (α * p0 - c) (α * p1 - c) (1 - p0 + p1) (1 - p1 + p0) d0 s0 d1 s1
      hlam hγ hx0 hx1 (by ring) hd0 hd1 hs0 hs1
    have h01 : α * (p0 + p1) - 2 * c = (α * p0 - c) + (α * p1 - c) := by ring
    have h10 : α * (p1 + p0) - 2 * c = (α * p1 - c) + (α * p0 - c) := by ring
    unfold dF sF
    rw [h01, h10]
    exact key

end CongestedPlatforms.Surge

open CongestedPlatforms.Surge

theorem solution (lam γ α c p0 p1 : ℝ) (hlam : 0 < lam) (hγ : 0 < γ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hc : 0 ≤ c) (hx0 : 0 < α * p0 - c) (hx1 : 0 < α * p1 - c) (hp0 : p0 < 1) (hp1 : p1 < 1) :
    (∀ d0 d1 s0 s1 : ℝ, 0 < d0 → 0 < d1 → 0 < s0 → 0 < s1 →
      ((d0 = lam * (1 - p0 - γ * (d0 / s0) ^ 2) ∧ d1 = lam * (1 - p1 - γ * (d1 / s1) ^ 2) ∧
          s0 = (α * p0 - c) * (d0 / s0) ∧ s1 = (α * p1 - c) * (d1 / s1)) ↔
        (d0 = dP lam γ α c p0 ∧ d1 = dP lam γ α c p1 ∧
          s0 = sP lam γ α c p0 ∧ s1 = sP lam γ α c p1))) ∧
    (1 - p0 - γ * (dP lam γ α c p0 / sP lam γ α c p0) ^ 2 ≤
        p1 + γ * (dP lam γ α c p1 / sP lam γ α c p1) ^ 2 ↔
      dP lam γ α c p0 + dP lam γ α c p1 ≤ lam) ∧
    (∀ d0 d1 s0 s1 : ℝ, 0 < d0 → 0 < d1 → 0 < s0 → 0 < s1 →
      ((d0 = 1 / 2 * lam * (1 - p0 + p1 - γ * ((d0 / s0) ^ 2 - (d1 / s1) ^ 2)) ∧
          d1 = 1 / 2 * lam * (1 - p1 + p0 - γ * ((d1 / s1) ^ 2 - (d0 / s0) ^ 2)) ∧
          s0 = (α * p0 - c) * (d0 / s0) ∧ s1 = (α * p1 - c) * (d1 / s1)) ↔
        (d0 = dF lam γ α c p0 p1 ∧ d1 = dF lam γ α c p1 p0 ∧
          s0 = sF lam γ α c p0 p1 ∧ s1 = sF lam γ α c p1 p0))) := by
  exact lemma_1_aux lam γ α c p0 p1 hlam hγ hα hα1 hc hx0 hx1 hp0 hp1
