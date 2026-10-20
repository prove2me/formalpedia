-- Prove2me | solution 2 for CohnElkies.lowerGammaBoundaryLog_halfInteger_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:46:50.205012+00:00
-- url     : https://prove2.me/submissions/bd2ccfb4-ae25-48b1-8df2-228de260ad90

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
theorem h47_normsq_Gamma_I (t : ℝ) (ht : t ≠ 0) :
    t * Real.sinh (Real.pi * t) * ‖Complex.Gamma (Complex.I * (t : ℂ))‖ ^ 2 = Real.pi := by
  set s : ℂ := Complex.I * (t : ℂ) with hsdef
  have hs0 : s ≠ 0 := by
    rw [hsdef]; exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast ht)
  have hc : (starRingEnd ℂ) s = -s := by
    rw [hsdef]; simp [Complex.conj_ofReal]
  have h1 := Complex.Gamma_mul_Gamma_one_sub s
  have h2 : Complex.Gamma (1 - s) = (starRingEnd ℂ) s * (starRingEnd ℂ) (Complex.Gamma s) := by
    rw [show (1 : ℂ) - s = -s + 1 by ring, Complex.Gamma_add_one _ (neg_ne_zero.mpr hs0), ← hc,
      Complex.Gamma_conj]
  rw [h2] at h1
  have h3 : Complex.sin (↑Real.pi * s) = ((Real.sinh (Real.pi * t) : ℝ) : ℂ) * Complex.I := by
    rw [hsdef, show (↑Real.pi : ℂ) * (Complex.I * ↑t) = ((Real.pi * t : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.sin_mul_I, Complex.ofReal_sinh]
  rw [h3] at h1
  have hsh : Real.sinh (Real.pi * t) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero ht
  have hne : ((Real.sinh (Real.pi * t) : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hsh) Complex.I_ne_zero
  have h4 : (Complex.Gamma s * ((starRingEnd ℂ) s * (starRingEnd ℂ) (Complex.Gamma s))) *
      (((Real.sinh (Real.pi * t) : ℝ) : ℂ) * Complex.I) = Real.pi := by
    rw [h1, div_mul_cancel₀ _ hne]
  have h5 : (Complex.Gamma s * ((starRingEnd ℂ) s * (starRingEnd ℂ) (Complex.Gamma s))) *
      (((Real.sinh (Real.pi * t) : ℝ) : ℂ) * Complex.I) =
      ((t * Real.sinh (Real.pi * t) * Complex.normSq (Complex.Gamma s) : ℝ) : ℂ) := by
    rw [show Complex.Gamma s * ((starRingEnd ℂ) s * (starRingEnd ℂ) (Complex.Gamma s)) =
        (starRingEnd ℂ) s * (Complex.Gamma s * (starRingEnd ℂ) (Complex.Gamma s)) by ring,
      Complex.mul_conj, hc, hsdef]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [h5] at h4
  rw [← Complex.normSq_eq_norm_sq]
  exact_mod_cast h4

theorem h47_normsq_Gamma_half (k : ℕ) (t : ℝ) :
    ‖Complex.Gamma ((((k : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) *
        ∏ j ∈ Finset.range k, (((j : ℝ) + 1 / 2) ^ 2 + t ^ 2) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_add, Finset.range_zero, Finset.prod_empty, mul_one]
    set s : ℂ := (((1 / 2 : ℝ)) : ℂ) + Complex.I * (t : ℂ) with hs
    have h1 : 1 - s = (starRingEnd ℂ) s := by
      apply Complex.ext <;> simp [hs] <;> norm_num
    have h2 := Complex.Gamma_mul_Gamma_one_sub s
    rw [h1, Complex.Gamma_conj, Complex.mul_conj] at h2
    have h3 : Complex.sin (↑Real.pi * s) = ((Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
      rw [show (↑Real.pi : ℂ) * s = ((Real.pi * t : ℝ) : ℂ) * Complex.I + ↑Real.pi / 2 by
        rw [hs]; push_cast; ring]
      rw [Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
    rw [h3] at h2
    rw [← Complex.normSq_eq_norm_sq]
    have h4 : ((Complex.normSq (Complex.Gamma s) : ℝ) : ℂ) =
        ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
      rw [h2]; push_cast; rfl
    exact_mod_cast h4
  | succ k ih =>
    set z : ℂ := (((k : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ) with hz
    have hz0 : z ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      rw [hz] at this
      simp at this
      have : (0:ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have he : ((((k + 1 : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ) = z + 1 := by
      rw [hz]; push_cast; ring
    have hn : ‖z‖ ^ 2 = ((k : ℝ) + 1 / 2) ^ 2 + t ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hz]
      simp
      ring
    rw [he, Complex.Gamma_add_one z hz0, norm_mul, mul_pow, ih, Finset.prod_range_succ, hn]
    ring

theorem solution
    (k : ℕ) (R : ℝ) :
    AntitoneOn (lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R)
      (Ioi (0 : ℝ)) := by
  intro y1 hy1 y2 hy2 hle
  have hy1' : (0:ℝ) < y1 := hy1
  have hy2' : (0:ℝ) < y2 := hy2
  unfold lowerGammaBoundaryLog
  have hp := Real.pi_pos
  -- values of the squared norms
  have hA : ∀ y : ℝ, 0 < y →
      (y / 2) * Real.sinh (Real.pi * (y / 2)) * ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ ^ 2
        = Real.pi := by
    intro y hy
    have h := h47_normsq_Gamma_I (-(y / 2)) (by intro h; linarith)
    rw [show Complex.I * ((-(y / 2) : ℝ) : ℂ) = -Complex.I * (y : ℂ) / 2 by push_cast; ring] at h
    rw [show Real.pi * -(y / 2) = -(Real.pi * (y / 2)) by ring, Real.sinh_neg] at h
    linarith [h]
  have hB : ∀ y : ℝ, ‖Complex.Gamma ((((k : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) / 2)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * (y / 2)) *
        ∏ j ∈ Finset.range k, (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2) := by
    intro y
    rw [← h47_normsq_Gamma_half k (y / 2)]
    congr 3
    push_cast; ring
  set A1 := ‖Complex.Gamma (-Complex.I * (y1 : ℂ) / 2)‖ with hA1d
  set A2 := ‖Complex.Gamma (-Complex.I * (y2 : ℂ) / 2)‖ with hA2d
  set B1 := ‖Complex.Gamma ((((k : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (y1 : ℂ) / 2)‖ with hB1d
  set B2 := ‖Complex.Gamma ((((k : ℝ) + 1 / 2 : ℝ) : ℂ) + Complex.I * (y2 : ℂ) / 2)‖ with hB2d
  have eA1 := hA y1 hy1'
  have eA2 := hA y2 hy2'
  have eB1 := hB y1
  have eB2 := hB y2
  try rw [← hA1d] at eA1
  try rw [← hA2d] at eA2
  try rw [← hB1d] at eB1
  try rw [← hB2d] at eB2
  set t1 := y1 / 2 with ht1
  set t2 := y2 / 2 with ht2
  have ht1p : 0 < t1 := by rw [ht1]; positivity
  have ht12 : t1 ≤ t2 := by rw [ht1, ht2]; linarith
  set s1 := Real.sinh (Real.pi * t1)
  set s2 := Real.sinh (Real.pi * t2)
  set c1 := Real.cosh (Real.pi * t1)
  set c2 := Real.cosh (Real.pi * t2)
  set P1 := ∏ j ∈ Finset.range k, (((j : ℝ) + 1 / 2) ^ 2 + t1 ^ 2)
  set P2 := ∏ j ∈ Finset.range k, (((j : ℝ) + 1 / 2) ^ 2 + t2 ^ 2)
  have hs1 : 0 < s1 := Real.sinh_pos_iff.mpr (by positivity)
  have hs2 : 0 < s2 := Real.sinh_pos_iff.mpr (by nlinarith)
  have hc1 : 0 < c1 := Real.cosh_pos _
  have hc2 : 0 < c2 := Real.cosh_pos _
  have hP1 : 0 < P1 := Finset.prod_pos fun j _ => by positivity
  have hP12 : P1 ≤ P2 := by
    apply Finset.prod_le_prod (fun j _ => by positivity)
    intro j _
    nlinarith
  have hsc : s1 * c2 ≤ s2 * c1 := by
    have h := Real.sinh_sub (Real.pi * t2) (Real.pi * t1)
    have hnn : 0 ≤ Real.sinh (Real.pi * t2 - Real.pi * t1) :=
      Real.sinh_nonneg_iff.mpr (by nlinarith)
    linarith
  have hkey : t1 * s1 * c2 * P1 ≤ t2 * s2 * c1 * P2 := by
    have h1 : t1 * (s1 * c2) ≤ t2 * (s2 * c1) :=
      mul_le_mul ht12 hsc (by positivity) (by linarith)
    have h2 := mul_le_mul h1 hP12 hP1.le (by nlinarith)
    linarith [h2]
  have hA1p : 0 < A1 := by
    have h0 : (0:ℝ) ≤ A1 := norm_nonneg _
    rcases h0.eq_or_lt with h | h
    · rw [← h] at eA1; simp at eA1; linarith
    · exact h
  have hA2p : 0 < A2 := by
    have h0 : (0:ℝ) ≤ A2 := norm_nonneg _
    rcases h0.eq_or_lt with h | h
    · rw [← h] at eA2; simp at eA2; linarith
    · exact h
  have hB1p : 0 < B1 := by
    have h0 : (0:ℝ) ≤ B1 := norm_nonneg _
    have hpos : 0 < B1 ^ 2 := by rw [eB1]; positivity
    rcases h0.eq_or_lt with h | h
    · rw [← h] at hpos; norm_num at hpos
    · exact h
  have hB2p : 0 < B2 := by
    have h0 : (0:ℝ) ≤ B2 := norm_nonneg _
    have hpos : 0 < B2 ^ 2 := by rw [eB2]; positivity
    rcases h0.eq_or_lt with h | h
    · rw [← h] at hpos; norm_num at hpos
    · exact h
  have eB1' : B1 ^ 2 * c1 = Real.pi * P1 := by rw [eB1]; field_simp
  have eB2' : B2 ^ 2 * c2 = Real.pi * P2 := by rw [eB2]; field_simp
  have hsq : (A2 * B1) ^ 2 ≤ (A1 * B2) ^ 2 := by
    have hM : 0 < t1 * s1 * t2 * s2 * c1 * c2 := by positivity
    refine le_of_mul_le_mul_right ?_ hM
    calc (A2 * B1) ^ 2 * (t1 * s1 * t2 * s2 * c1 * c2)
        = (t2 * s2 * A2 ^ 2) * (B1 ^ 2 * c1) * (t1 * s1 * c2) := by ring
      _ = Real.pi * (Real.pi * P1) * (t1 * s1 * c2) := by rw [eA2, eB1']
      _ = Real.pi * Real.pi * (t1 * s1 * c2 * P1) := by ring
      _ ≤ Real.pi * Real.pi * (t2 * s2 * c1 * P2) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (t1 * s1 * A1 ^ 2) * (B2 ^ 2 * c2) * (t2 * s2 * c1) := by rw [eA1, eB2']; ring
      _ = (A1 * B2) ^ 2 * (t1 * s1 * t2 * s2 * c1 * c2) := by ring
  have hprod : A2 * B1 ≤ A1 * B2 :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have hlog := Real.log_le_log (by positivity) hprod
  rw [Real.log_mul hA2p.ne' hB1p.ne', Real.log_mul hA1p.ne' hB2p.ne'] at hlog
  linarith

