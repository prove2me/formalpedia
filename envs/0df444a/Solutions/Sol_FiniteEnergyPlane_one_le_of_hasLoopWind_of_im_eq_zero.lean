-- Prove2me | solution 1 for FiniteEnergyPlane.one_le_of_hasLoopWind_of_im_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T21:20:26.162867+00:00
-- url     : https://prove2.me/submissions/41d20e23-ca86-4161-a829-f9209c4225c4

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.Analysis.Calculus.Deriv.Slope



namespace FiniteEnergyPlane

open Filter Topology
open scoped Real

theorem wlb_barrier {g : ℝ → ℂ} {θ : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hg0 : ∀ t, g t ≠ 0)
    (hθc : Continuous θ) (hθ : ∀ t, g t = (‖g t‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I))
    (hd : ∀ t, HasDerivAt (fun s => (g s).im) (c * (g t).re) t) (m : ℤ) {s t : ℝ}
    (hst : s < t) (hs : 2 * π * m ≤ θ s) : 2 * π * m < θ t := by
  have hpi := Real.pi_pos
  have him : ∀ t, (g t).im = ‖g t‖ * Real.sin (θ t) := by
    intro t
    conv_lhs => rw [hθ t]
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hre : ∀ t, (g t).re = ‖g t‖ * Real.cos (θ t) := by
    intro t
    conv_lhs => rw [hθ t]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hsc : ∀ x, 2 * π * m = θ x → Real.sin (θ x) = 0 ∧ Real.cos (θ x) = 1 := by
    intro x heq
    rw [← heq, show 2 * π * (m : ℝ) = (m : ℝ) * (2 * π) by ring]
    exact ⟨by simpa using Real.sin_sub_int_mul_two_pi 0 m, Real.cos_int_mul_two_pi m⟩
  have hbar : Set.Icc s t ⊆ {x | 2 * π * m ≤ θ x} := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsWithin
    · exact (isClosed_le continuous_const hθc).inter isClosed_Icc
    · exact hs
    · rintro x ⟨hx, -⟩
      simp only [Set.mem_setOf_eq] at hx
      rcases hx.lt_or_eq with hlt | heq
      · filter_upwards [nhdsWithin_le_nhds ((isOpen_lt continuous_const hθc).mem_nhds hlt)]
          with t ht using le_of_lt ht
      · obtain ⟨hsin, hcos⟩ := hsc x heq
        have hgx : 0 < ‖g x‖ := norm_pos_iff.2 (hg0 x)
        have hderpos : 0 < c * (g x).re := by rw [hre, hcos, mul_one]; positivity
        have hslope := hasDerivWithinAt_iff_tendsto_slope.1
          ((hd x).hasDerivWithinAt (s := Set.Ioi x))
        rw [Set.diff_singleton_eq_self (s := Set.Ioi x) (lt_irrefl x)] at hslope
        have hev1 : ∀ᶠ t in 𝓝[>] x, 0 < slope (fun s => (g s).im) x t :=
          hslope.eventually (lt_mem_nhds hderpos)
        have hev2 : ∀ᶠ t in 𝓝[>] x, θ t ∈ Set.Ioo (θ x - π) (θ x + π) :=
          nhdsWithin_le_nhds ((hθc.tendsto x) (Ioo_mem_nhds (by linarith) (by linarith)))
        filter_upwards [hev1, hev2, self_mem_nhdsWithin] with t h1 h2 h3
        have himx : (g x).im = 0 := by rw [him, hsin, mul_zero]
        rw [slope_def_field, himx, sub_zero] at h1
        have htx : 0 < t - x := sub_pos.2 h3
        have ht : 0 < (g t).im := by
          by_contra hn
          push_neg at hn
          exact absurd h1 (not_lt.2 (div_nonpos_of_nonpos_of_nonneg hn htx.le))
        rw [him] at ht
        have hs : 0 < Real.sin (θ t) := pos_of_mul_pos_right ht (norm_nonneg _)
        show 2 * π * m ≤ θ t
        by_contra hneg
        push_neg at hneg
        have hsn : Real.sin (θ t) ≤ 0 := by
          rw [← Real.sin_sub_int_mul_two_pi (θ t) m]
          apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
          · linarith
          · have := h2.1
            linarith
        linarith
  have ht : 2 * π * m ≤ θ t := hbar ⟨hst.le, le_rfl⟩
  rcases ht.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  obtain ⟨hsin, hcos⟩ := hsc t heq
  have hgt : 0 < ‖g t‖ := norm_pos_iff.2 (hg0 t)
  have hderpos : 0 < c * (g t).re := by rw [hre, hcos, mul_one]; positivity
  have hslope := hasDerivWithinAt_iff_tendsto_slope.1
    ((hd t).hasDerivWithinAt (s := Set.Iio t))
  rw [Set.diff_singleton_eq_self (s := Set.Iio t) (lt_irrefl t)] at hslope
  have hev1 : ∀ᶠ x in 𝓝[<] t, 0 < slope (fun s => (g s).im) t x :=
    hslope.eventually (lt_mem_nhds hderpos)
  have hev2 : ∀ᶠ x in 𝓝[<] t, θ x < θ t + π :=
    nhdsWithin_le_nhds ((hθc.tendsto t) (Iio_mem_nhds (by linarith)))
  have hev3 : ∀ᶠ x in 𝓝[<] t, s < x := nhdsWithin_le_nhds (Ioi_mem_nhds hst)
  obtain ⟨x, h1, h2, h3, h4⟩ :=
    (hev1.and (hev2.and (hev3.and self_mem_nhdsWithin))).exists
  have himt : (g t).im = 0 := by rw [him, hsin, mul_zero]
  rw [slope_def_field, himt, sub_zero] at h1
  have hxt : x - t < 0 := sub_neg.2 h4
  have hneg : (g x).im < 0 := by
    by_contra hn
    push_neg at hn
    exact absurd h1 (not_lt.2 (div_nonpos_of_nonneg_of_nonpos hn hxt.le))
  have hθx : 2 * π * m ≤ θ x := hbar ⟨h3.le, (Set.mem_Iio.1 h4).le⟩
  rw [him] at hneg
  have hsx : 0 ≤ Real.sin (θ x) := by
    rw [← Real.sin_sub_int_mul_two_pi (θ x) m]
    apply Real.sin_nonneg_of_nonneg_of_le_pi <;> linarith
  have : 0 ≤ ‖g x‖ * Real.sin (θ x) := mul_nonneg (norm_nonneg _) hsx
  linarith

theorem wlb_pos {g : ℝ → ℂ} {θ : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hg0 : ∀ t, g t ≠ 0)
    (hθc : Continuous θ) (hθ : ∀ t, g t = (‖g t‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I))
    (hd : ∀ t, HasDerivAt (fun s => (g s).im) (c * (g t).re) t) (m : ℤ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hu : θ u = 2 * π * m) : θ 0 < θ 1 := by
  have h1 := wlb_barrier hc hg0 hθc hθ hd m hu1 hu.ge
  have h0 : θ 0 ≤ 2 * π * m := by
    rcases hu0.lt_or_eq with h | h
    · by_contra hn
      push_neg at hn
      have := wlb_barrier hc hg0 hθc hθ hd m h hn.le
      linarith
    · rw [h, hu]
  linarith

theorem one_le_of_hasLoopWind_of_im_eq_zero_aux {g : ℝ → ℂ} {k : ℤ} {c : ℝ}
    (hg : HasLoopWind g k) (hc : 0 < c)
    (hd : ∀ t, HasDerivAt (fun s => (g s).im) (c * (g t).re) t) {t₀ : ℝ}
    (ht₀ : (g t₀).im = 0) : 1 ≤ k := by
  obtain ⟨-, hper, hg0, θ, hθc, hθ, hθk⟩ := hg
  have hpi := Real.pi_pos
  set u := Int.fract t₀ with hu_def
  have hu0 : 0 ≤ u := Int.fract_nonneg _
  have hu1 : u < 1 := Int.fract_lt_one _
  have hgu : g u = g t₀ := by
    have := hper.sub_int_mul_eq (n := ⌊t₀⌋) (x := t₀)
    rw [mul_one] at this
    rw [hu_def, Int.fract, this]
  have hsin : Real.sin (θ u) = 0 := by
    have him : (g u).im = ‖g u‖ * Real.sin (θ u) := by
      conv_lhs => rw [hθ u]
      rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    rw [hgu, ht₀] at him
    rcases mul_eq_zero.1 him.symm with h | h
    · exact absurd (norm_eq_zero.1 h) (hgu ▸ hg0 u)
    · exact h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hsin
  have hlt : θ 0 < θ 1 := by
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
    · exact wlb_pos hc hg0 hθc hθ hd m hu0 hu1 (by rw [← hn]; push_cast; ring)
    · have key := wlb_pos (g := fun t => -g t) (θ := fun t => θ t + π) hc
        (fun t => neg_ne_zero.2 (hg0 t)) (hθc.add continuous_const)
        (fun t => by
          rw [norm_neg, Complex.ofReal_add, add_mul, Complex.exp_add,
            Complex.exp_pi_mul_I, hθ t]
          simp only [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
            norm_norm]
          ring)
        (fun t => by
          have := (hd t).neg
          simp only [Complex.neg_im, Complex.neg_re, mul_neg] at this ⊢
          exact this)
        (m + 1) hu0 hu1 (by rw [← hn]; push_cast; ring)
      simpa using key
  have : (0 : ℝ) < k := by
    have h2 : 0 < 2 * π * (k : ℝ) := by linarith
    exact (mul_pos_iff_of_pos_left (by positivity)).1 h2
  exact_mod_cast this

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {g : ℝ → ℂ} {k : ℤ} {c : ℝ}
    (hg : HasLoopWind g k) (hc : 0 < c)
    (hd : ∀ t, HasDerivAt (fun s => (g s).im) (c * (g t).re) t) {t₀ : ℝ}
    (ht₀ : (g t₀).im = 0) : 1 ≤ k :=
  one_le_of_hasLoopWind_of_im_eq_zero_aux hg hc hd ht₀
