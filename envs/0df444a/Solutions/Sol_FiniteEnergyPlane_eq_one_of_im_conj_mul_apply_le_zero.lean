-- Prove2me | solution 1 for FiniteEnergyPlane.eq_one_of_im_conj_mul_apply_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T22:27:18.994199+00:00
-- url     : https://prove2.me/submissions/95a02cf1-f958-444e-90f6-794ec5835735

import Mathlib



namespace FiniteEnergyPlane

open Filter Topology ComplexConjugate

theorem eq_one_of_im_conj_mul_apply_le_zero_aux {L : ℂ →ₗ[ℝ] ℂ}
    (hL : ∀ z w, (conj (L z) * L w).im = (conj z * w).im) {α c : ℝ} (hc : 0 < c)
    (hu : L (Complex.exp (α * Complex.I)) = c * Complex.exp (α * Complex.I))
    (hsign : (∀ᶠ β : ℝ in 𝓝 α, (conj (Complex.exp ((β : ℂ) * Complex.I)) *
        L (Complex.exp ((β : ℂ) * Complex.I))).im ≤ 0) ∨
      (∀ᶠ β : ℝ in 𝓝 α, 0 ≤ (conj (Complex.exp ((β : ℂ) * Complex.I)) *
        L (Complex.exp ((β : ℂ) * Complex.I))).im)) : c = 1 := by
  set u := Complex.exp (α * Complex.I) with hudef
  set w := Complex.I * u with hwdef
  have hu1 : conj u * u = 1 := by
    rw [Complex.conj_mul', hudef, Complex.norm_exp_ofReal_mul_I]; simp
  set A := L u
  set B := L w
  -- the quadratic form along the circle through `u`
  have hexp : ∀ ε : ℝ, Complex.exp (((α + ε : ℝ) : ℂ) * Complex.I) =
      (Real.cos ε : ℂ) * u + (Real.sin ε : ℂ) * w := by
    intro ε
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, hwdef, hudef,
      Complex.exp_mul_I (ε : ℂ), ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have hLv : ∀ a b : ℝ, L ((a : ℂ) * u + (b : ℂ) * w) = (a : ℂ) * A + (b : ℂ) * B := by
    intro a b
    rw [← Complex.real_smul, ← Complex.real_smul, map_add, map_smul, map_smul,
      Complex.real_smul, Complex.real_smul]
  have hquad : ∀ a b : ℝ, (conj ((a : ℂ) * u + (b : ℂ) * w) * ((a : ℂ) * A + (b : ℂ) * B)).im =
      a ^ 2 * (conj u * A).im + a * b * ((conj u * B).im + (conj w * A).im) +
        b ^ 2 * (conj w * B).im := by
    intro a b
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.mul_im, Complex.mul_re,
      Complex.add_im, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hAu : A = c * u := hu
  have h1 : (conj u * A).im = 0 := by
    rw [hAu, mul_left_comm, hu1]; simp
  have h2 : (conj w * A).im = -c := by
    rw [hAu, hwdef, map_mul, Complex.conj_I]
    have : -Complex.I * conj u * (c * u) = -(c : ℂ) * Complex.I * (conj u * u) := by ring
    rw [this, hu1]; simp
  have h3 : c * (conj u * B).im = 1 := by
    have h := hL u w
    change (conj A * B).im = (conj u * w).im at h
    have e1 : (conj u * w).im = 1 := by rw [hwdef, mul_left_comm, hu1]; simp
    have e2 : conj A * B = (c : ℂ) * (conj u * B) := by
      rw [hAu, map_mul, Complex.conj_ofReal]; ring
    rw [e2, Complex.im_ofReal_mul, e1] at h
    exact h
  set p := (conj u * B).im
  set Q := (conj w * B).im
  set g : ℝ → ℝ := fun ε => Real.cos ε * (p - c) + Real.sin ε * Q with hg
  have hf : ∀ ε : ℝ, (conj (Complex.exp (((α + ε : ℝ) : ℂ) * Complex.I)) *
      L (Complex.exp (((α + ε : ℝ) : ℂ) * Complex.I))).im = Real.sin ε * g ε := by
    intro ε
    rw [hexp, hLv, hquad, h1, h2]
    simp only [hg]
    ring
  have hgc : Continuous g := by
    simp only [hg]; fun_prop
  have hg0 : g 0 = p - c := by simp [hg]
  have htend : Tendsto (fun ε : ℝ => α + ε) (𝓝 0) (𝓝 α) := by
    have h : Tendsto (fun ε : ℝ => α + ε) (𝓝 0) (𝓝 (α + 0)) :=
      tendsto_const_nhds.add tendsto_id
    simpa using h
  have hsign' : (∀ᶠ ε in 𝓝 (0 : ℝ), Real.sin ε * g ε ≤ 0) ∨
      (∀ᶠ ε in 𝓝 (0 : ℝ), 0 ≤ Real.sin ε * g ε) := by
    rcases hsign with h | h
    · left
      have h' := htend.eventually h
      filter_upwards [h'] with ε hε
      rw [← hf]; exact hε
    · right
      have h' := htend.eventually h
      filter_upwards [h'] with ε hε
      rw [← hf]; exact hε
  have hsinR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < Real.sin ε := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi from Real.pi_pos)] with ε hε
    exact Real.sin_pos_of_pos_of_lt_pi hε.1 hε.2
  have hsinL : ∀ᶠ ε in 𝓝[<] (0 : ℝ), Real.sin ε < 0 := by
    filter_upwards [Ioo_mem_nhdsLT (show -Real.pi < (0 : ℝ) by linarith [Real.pi_pos])]
      with ε hε
    exact Real.sin_neg_of_neg_of_neg_pi_lt hε.2 hε.1
  have hpc : p = c := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hgneg : ∀ᶠ ε in 𝓝 (0 : ℝ), g ε < 0 :=
        hgc.continuousAt.eventually_lt continuous_const.continuousAt (by rw [hg0]; linarith)
      rcases hsign' with h | h
      · obtain ⟨ε, h1, h2, h3⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
          ((hgneg.filter_mono nhdsWithin_le_nhds).and hsinL)).exists
        nlinarith
      · obtain ⟨ε, h1, h2, h3⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
          ((hgneg.filter_mono nhdsWithin_le_nhds).and hsinR)).exists
        nlinarith
    · have hgpos : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < g ε :=
        continuous_const.continuousAt.eventually_lt hgc.continuousAt (by rw [hg0]; linarith)
      rcases hsign' with h | h
      · obtain ⟨ε, h1, h2, h3⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
          ((hgpos.filter_mono nhdsWithin_le_nhds).and hsinR)).exists
        nlinarith
      · obtain ⟨ε, h1, h2, h3⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
          ((hgpos.filter_mono nhdsWithin_le_nhds).and hsinL)).exists
        nlinarith
  rw [hpc] at h3
  nlinarith

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology ComplexConjugate

theorem solution {L : ℂ →ₗ[ℝ] ℂ}
    (hL : ∀ z w, (conj (L z) * L w).im = (conj z * w).im) {α c : ℝ} (hc : 0 < c)
    (hu : L (Complex.exp (α * Complex.I)) = c * Complex.exp (α * Complex.I))
    (hsign : (∀ᶠ β : ℝ in 𝓝 α, (conj (Complex.exp ((β : ℂ) * Complex.I)) *
        L (Complex.exp ((β : ℂ) * Complex.I))).im ≤ 0) ∨
      (∀ᶠ β : ℝ in 𝓝 α, 0 ≤ (conj (Complex.exp ((β : ℂ) * Complex.I)) *
        L (Complex.exp ((β : ℂ) * Complex.I))).im)) : c = 1 :=
  eq_one_of_im_conj_mul_apply_le_zero_aux hL hc hu hsign
