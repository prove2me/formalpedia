-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopWind_triangular_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T15:10:30.676126+00:00
-- url     : https://prove2.me/submissions/9bf5ecf6-5255-4033-9bc5-9ff746a33426

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_exists_hasLoopWind
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_conj
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_zero_of_forall_ne_ray



namespace FiniteEnergyPlane

open scoped Real

theorem hasLoopWind_triangular_iff_aux {a b d : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hd : Continuous d) (hap : Function.Periodic a 1) (hbp : Function.Periodic b 1)
    (hdp : Function.Periodic d 1) (ha0 : ∀ t, 0 < a t) (hd0 : ∀ t, 0 < d t) {z : ℝ → ℂ}
    (hz : Continuous z) (hzp : Function.Periodic z 1) (hz0 : ∀ t, z t ≠ 0) (k : ℤ) :
    HasLoopWind (fun t => ((a t * (z t).re + b t * (z t).im : ℝ) : ℂ) +
        ((d t * (z t).im : ℝ) : ℂ) * Complex.I) k ↔ HasLoopWind z k := by
  set f : ℝ → ℂ := fun t => ((a t * (z t).re + b t * (z t).im : ℝ) : ℂ) +
    ((d t * (z t).im : ℝ) : ℂ) * Complex.I with hfdef
  have hfc : Continuous f := by
    rw [hfdef]
    fun_prop
  have hfp : Function.Periodic f 1 := by
    intro t; simp only [hfdef, hap t, hbp t, hdp t, hzp t]
  have hfre : ∀ t, (f t).re = a t * (z t).re + b t * (z t).im := fun t => by simp [hfdef]
  have hfim : ∀ t, (f t).im = d t * (z t).im := fun t => by simp [hfdef]
  have hf0 : ∀ t, f t ≠ 0 := by
    intro t h
    have h1 := hfim t; have h2 := hfre t
    rw [h, Complex.zero_im] at h1; rw [h, Complex.zero_re] at h2
    have him : (z t).im = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact absurd h (hd0 t).ne'
      · exact h
    have hre : (z t).re = 0 := by
      rw [him, mul_zero, add_zero] at h2
      rcases mul_eq_zero.1 h2.symm with h | h
      · exact absurd h (ha0 t).ne'
      · exact h
    exact hz0 t (Complex.ext hre him)
  obtain ⟨kf, hkf⟩ := exists_hasLoopWind f hfc hfp hf0
  obtain ⟨kz, hkz⟩ := exists_hasLoopWind z hz hzp hz0
  -- the auxiliary loop `w = (a + d) + i b` has winding `0`
  set w : ℝ → ℂ := fun t => ((a t + d t : ℝ) : ℂ) + (b t : ℂ) * Complex.I with hwdef
  have hw : HasLoopWind w 0 := by
    refine hasLoopWind_zero_of_forall_ne_ray w (by rw [hwdef]; fun_prop)
      (fun t => by simp only [hwdef, hap t, hbp t, hdp t]) (-1) (by norm_num) ?_
    intro t s hs h
    have := congrArg Complex.re h
    simp [hwdef] at this
    linarith [ha0 t, hd0 t]
  have hg := hasLoopWind_mul (hasLoopWind_mul hkf (hasLoopWind_conj hkz)) hw
  have hg0 : HasLoopWind (fun t => f t * starRingEnd ℂ (z t) * w t) 0 := by
    refine hasLoopWind_zero_of_forall_ne_ray _ hg.1 hg.2.1 (-1) (by norm_num) ?_
    intro t s hs h
    have hre := congrArg Complex.re h
    have hzne : (z t).re ^ 2 + (z t).im ^ 2 ≠ 0 := by
      intro h0
      apply hz0 t
      apply Complex.ext
      · simp; nlinarith [sq_nonneg (z t).re, sq_nonneg (z t).im]
      · simp; nlinarith [sq_nonneg (z t).re, sq_nonneg (z t).im]
    have hpos : 0 < (z t).re ^ 2 + (z t).im ^ 2 :=
      lt_of_le_of_ne (by positivity) (Ne.symm hzne)
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, hfre, hfim,
      hwdef, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.one_re] at hre
    have ha := ha0 t; have hd := hd0 t
    set q := (z t).re; set p := (z t).im
    -- `Re = a(a+d) q² + 2ab pq + (d(a+d)+b²) p²`, a positive definite form
    have key : 0 < a t * (a t + d t) * q ^ 2 + 2 * a t * b t * p * q +
        (d t * (a t + d t) + b t ^ 2) * p ^ 2 := by
      have e : (a t + d t) * (a t * (a t + d t) * q ^ 2 + 2 * a t * b t * p * q +
          (d t * (a t + d t) + b t ^ 2) * p ^ 2) =
          ((a t + d t) * a t * q + a t * b t * p) ^ 2 / a t +
          d t * (a t + d t) ^ 2 * p ^ 2 + d t * b t ^ 2 * p ^ 2 := by
        field_simp; ring
      have hsum : 0 < ((a t + d t) * a t * q + a t * b t * p) ^ 2 / a t +
          d t * (a t + d t) ^ 2 * p ^ 2 + d t * b t ^ 2 * p ^ 2 := by
        rcases eq_or_ne p 0 with hp | hp
        · have hq : q ≠ 0 := by
            intro hq; rw [hp, hq] at hpos; norm_num at hpos
          rw [hp]
          have : 0 < ((a t + d t) * a t * q + a t * b t * 0) ^ 2 := by
            have : (a t + d t) * a t * q ≠ 0 := by
              have : 0 < (a t + d t) * a t := by positivity
              exact mul_ne_zero this.ne' hq
            simpa using pow_pos (abs_pos.2 this) 2 |>.trans_eq (sq_abs _)
          have := div_pos this ha
          nlinarith [sq_nonneg (b t)]
        · have h1 : 0 ≤ ((a t + d t) * a t * q + a t * b t * p) ^ 2 / a t :=
            div_nonneg (sq_nonneg _) ha.le
          have h2 : 0 < d t * (a t + d t) ^ 2 * p ^ 2 := by positivity
          have h3 : 0 ≤ d t * b t ^ 2 * p ^ 2 := by positivity
          linarith
      have hc : 0 < a t + d t := by linarith
      rw [← e] at hsum
      exact pos_of_mul_pos_right hsum hc.le
    nlinarith
  have hk : kf + -kz + 0 = 0 := hasLoopWind_unique hg hg0
  have hkk : kf = kz := by omega
  constructor
  · intro h
    have := hasLoopWind_unique h hkf
    rw [this, hkk]; exact hkz
  · intro h
    have := hasLoopWind_unique h hkz
    rw [this, ← hkk]; exact hkf

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {a b d : ℝ → ℝ} (ha : Continuous a) (hb : Continuous b)
    (hd : Continuous d) (hap : Function.Periodic a 1) (hbp : Function.Periodic b 1)
    (hdp : Function.Periodic d 1) (ha0 : ∀ t, 0 < a t) (hd0 : ∀ t, 0 < d t) {z : ℝ → ℂ}
    (hz : Continuous z) (hzp : Function.Periodic z 1) (hz0 : ∀ t, z t ≠ 0) (k : ℤ) :
    HasLoopWind (fun t => ((a t * (z t).re + b t * (z t).im : ℝ) : ℂ) +
        ((d t * (z t).im : ℝ) : ℂ) * Complex.I) k ↔ HasLoopWind z k :=
  hasLoopWind_triangular_iff_aux ha hb hd hap hbp hdp ha0 hd0 hz hzp hz0 k
