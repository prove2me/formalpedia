-- Prove2me | solution 1 for BirkhoffGlobalSection.numerical_range_subcritical
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:52:20.88934+00:00
-- url     : https://prove2.me/submissions/3070af12-e85a-4c04-8ff8-b08a1b498ccd

import Mathlib
import Definitions.Def_BirkhoffGlobalSection

namespace BirkhoffGlobalSection

lemma dir_zero {F : Phase → ℝ} {s : Phase} (h : isCriticalPoint F s) (v : Phase)
    {D : ℝ} (hD : HasDerivAt (fun t : ℝ => F (s + t • v)) D 0) : D = 0 := by
  obtain ⟨hdiff, hzero⟩ := h
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  have hline : HasDerivAt (fun t : ℝ => s + t • v) v 0 := by
    have := HasDerivAt.const_add s (HasDerivAt.smul_const hid v)
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => F (s + t • v)) (fderiv ℝ F s v) 0 := by
    have := HasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hdiff.hasFDerivAt hline (by simp)
    simpa [Function.comp_def] using this
  have := HasDerivAt.unique hD h2
  rw [this, hzero]; rfl

lemma hasDerivAt_invsqrt (c d : ℝ) (h : 0 < c ^ 2 + d) :
    HasDerivAt (fun t : ℝ => (Real.sqrt ((c + t) ^ 2 + d))⁻¹)
      (-(c / (Real.sqrt (c ^ 2 + d)) ^ 3)) 0 := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  have hg0 := HasDerivAt.add_const d (HasDerivAt.pow (HasDerivAt.const_add c hid) 2)
  have hg : HasDerivAt (fun t : ℝ => (c + t) ^ 2 + d) (2 * c) 0 :=
    HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq hg0
      (Filter.Eventually.of_forall fun t => by simp)) (by simp)
  have hne : (fun t : ℝ => (c + t) ^ 2 + d) 0 ≠ 0 := by simp; linarith
  have hs := HasDerivAt.sqrt hg hne
  have hsne : (fun t : ℝ => Real.sqrt ((c + t) ^ 2 + d)) 0 ≠ 0 := by
    simp only [add_zero]; exact (Real.sqrt_pos.2 h).ne'
  have hi := HasDerivAt.inv hs hsne
  have hp : Real.sqrt (c ^ 2 + d) ≠ 0 := (Real.sqrt_pos.2 h).ne'
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq hi
      (Filter.Eventually.of_forall fun t => by simp)) ?_
  simp only [add_zero]
  field_simp

lemma crit_eqs (μ : ℝ) (s : Phase) (hcf : collisionFree μ s)
    (hc : isCriticalPoint (jacobiHamiltonian μ) s) :
    s 2 = s 1 ∧ s 3 = - s 0 ∧
    s 3 + (1 - μ) * ((s 0 + μ) / (Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)) ^ 3)
        + μ * ((s 0 - 1 + μ) / (Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2)) ^ 3) = 0 ∧
    - s 2 + (1 - μ) * (s 1 / (Real.sqrt ((s 1) ^ 2 + (s 0 + μ) ^ 2)) ^ 3)
        + μ * (s 1 / (Real.sqrt ((s 1) ^ 2 + (s 0 - 1 + μ) ^ 2)) ^ 3) = 0 := by
  obtain ⟨ha, hb⟩ := hcf
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  refine ⟨?_, ?_, ?_, ?_⟩
  · have key := HasDerivAt.sub (HasDerivAt.div_const
        (HasDerivAt.add_const (s 3 ^ 2) (HasDerivAt.pow (HasDerivAt.const_add (s 2) hid) 2)) 2)
      (HasDerivAt.const_mul (s 1) (HasDerivAt.const_add (s 2) hid))
    have hD : HasDerivAt (fun t : ℝ => jacobiHamiltonian μ (s + t • coordinateVector 2))
        (s 2 - s 1) 0 :=
      HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq
        (HasDerivAt.add_const (s 0 * s 3 - (1 - μ) / Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)
            - μ / Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2)) key)
        (Filter.Eventually.of_forall fun t => by
          simp [jacobiHamiltonian, coordinateVector]; ring)) (by simp)
    have := dir_zero hc _ hD
    linarith
  · have key := HasDerivAt.add (HasDerivAt.div_const
        (HasDerivAt.const_add (s 2 ^ 2) (HasDerivAt.pow (HasDerivAt.const_add (s 3) hid) 2)) 2)
      (HasDerivAt.const_mul (s 0) (HasDerivAt.const_add (s 3) hid))
    have hD : HasDerivAt (fun t : ℝ => jacobiHamiltonian μ (s + t • coordinateVector 3))
        (s 3 + s 0) 0 :=
      HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq
        (HasDerivAt.add_const (- s 1 * s 2 - (1 - μ) / Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)
            - μ / Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2)) key)
        (Filter.Eventually.of_forall fun t => by
          simp [jacobiHamiltonian, coordinateVector]; ring)) (by simp)
    have := dir_zero hc _ hD
    linarith
  · have hA := hasDerivAt_invsqrt (s 0 + μ) (s 1 ^ 2) ha
    have hB := hasDerivAt_invsqrt (s 0 - 1 + μ) (s 1 ^ 2) hb
    have key := HasDerivAt.sub (HasDerivAt.sub
      (HasDerivAt.mul_const (HasDerivAt.const_add (s 0) hid) (s 3))
      (HasDerivAt.const_mul (1 - μ) hA)) (HasDerivAt.const_mul μ hB)
    have hD : HasDerivAt (fun t : ℝ => jacobiHamiltonian μ (s + t • coordinateVector 0))
        (s 3 + (1 - μ) * ((s 0 + μ) / (Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)) ^ 3)
        + μ * ((s 0 - 1 + μ) / (Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2)) ^ 3)) 0 :=
      HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq
        (HasDerivAt.add_const ((s 2 ^ 2 + s 3 ^ 2) / 2 - s 1 * s 2) key)
        (Filter.Eventually.of_forall fun t => by
          simp [jacobiHamiltonian, coordinateVector, div_eq_mul_inv]; ring_nf))
        (by simp)
    exact dir_zero hc _ hD
  · have ha' : 0 < s 1 ^ 2 + (s 0 + μ) ^ 2 := by linarith
    have hb' : 0 < s 1 ^ 2 + (s 0 - 1 + μ) ^ 2 := by linarith
    have hA := hasDerivAt_invsqrt (s 1) ((s 0 + μ) ^ 2) ha'
    have hB := hasDerivAt_invsqrt (s 1) ((s 0 - 1 + μ) ^ 2) hb'
    have key := HasDerivAt.add (HasDerivAt.add
      (HasDerivAt.mul_const (HasDerivAt.const_add (s 1) hid) (s 2))
      (HasDerivAt.const_mul (1 - μ) hA)) (HasDerivAt.const_mul μ hB)
    have hD : HasDerivAt (fun t : ℝ => jacobiHamiltonian μ (s + t • coordinateVector 1))
        (- s 2 + (1 - μ) * (s 1 / (Real.sqrt ((s 1) ^ 2 + (s 0 + μ) ^ 2)) ^ 3)
        + μ * (s 1 / (Real.sqrt ((s 1) ^ 2 + (s 0 - 1 + μ) ^ 2)) ^ 3)) 0 :=
      HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq
        (HasDerivAt.const_sub ((s 2 ^ 2 + s 3 ^ 2) / 2 + s 0 * s 3) key)
        (Filter.Eventually.of_forall fun t => by
          simp [jacobiHamiltonian, coordinateVector, div_eq_mul_inv]; ring_nf))
        (by simp; ring)
    exact dir_zero hc _ hD

lemma tan_inv (r r' : ℝ) (hr : 0 < r) (hr' : 0 < r') : 1 / r - (r' - r) / r ^ 2 ≤ 1 / r' := by
  have h : 1 / r' - (1 / r - (r' - r) / r ^ 2) = (r' - r) ^ 2 / (r ^ 2 * r') := by
    field_simp; ring
  have : 0 ≤ (r' - r) ^ 2 / (r ^ 2 * r') := by positivity
  linarith

set_option maxHeartbeats 4000000 in
/-- the three collinear cases, in terms of the axis coordinate `x` -/
lemma axis_bound (μ x : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 2)
    (hu : x + μ ≠ 0) (hv : x - 1 + μ ≠ 0)
    (hE : -x + (1 - μ) * ((x + μ) / |x + μ| ^ 3) + μ * ((x - 1 + μ) / |x - 1 + μ| ^ 3) = 0) :
    x ^ 2 / 2 + (1 - μ) / |x + μ| + μ / |x - 1 + μ| ≤ 209 / 100 := by
  rcases lt_or_gt_of_ne hu with hu' | hu'
  · -- left of the large primary
    have hv' : x - 1 + μ < 0 := by linarith
    rw [abs_of_neg hu', abs_of_neg hv'] at hE ⊢
    set r1 := -(x + μ) with hr1
    set r2 := -(x - 1 + μ) with hr2
    have h1 : 0 < r1 := by linarith
    have h2 : 0 < r2 := by linarith
    set A := (1 - μ) / r1 ^ 2
    set B := μ / r2 ^ 2
    have hE' : -x - A - B = 0 := by
      have e1 : (1 - μ) * ((x + μ) / r1 ^ 3) = -A := by
        simp only [A, hr1]; field_simp
      have e2 : μ * ((x - 1 + μ) / r2 ^ 3) = -B := by
        simp only [B, hr2]; field_simp
      linarith
    set w : ℝ := -1 - μ
    have t1 := tan_inv r1 1 h1 one_pos
    have t2 := tan_inv r2 2 h2 two_pos
    have c1 := mul_le_mul_of_nonneg_left t1 (by linarith : (0:ℝ) ≤ 1 - μ)
    have c2 := mul_le_mul_of_nonneg_left t2 hμ0.le
    have e1 : (1 - μ) * (1 / r1 - (1 - r1) / r1 ^ 2) = (1 - μ) / r1 + (w - x) * A := by
      simp only [A, w, hr1]; field_simp; ring
    have e2 : μ * (1 / r2 - (2 - r2) / r2 ^ 2) = μ / r2 + (w - x) * B := by
      simp only [B, w, hr2]; field_simp; ring
    have e3 : (w - x) * A + (w - x) * B + x * (w - x) = 0 := by
      rw [show A = -x - B by linarith]; ring
    have hsq : x ^ 2 / 2 + x * (w - x) ≤ w ^ 2 / 2 := by nlinarith [sq_nonneg (w - x)]
    have hw : w ^ 2 / 2 + (1 - μ) * (1 / 1) + μ * (1 / 2) ≤ 209 / 100 := by
      simp only [w]; nlinarith
    rw [e1] at c1; rw [e2] at c2
    linarith
  · have hv0 : x - 1 + μ < 0 ∨ 0 < x - 1 + μ := lt_or_gt_of_ne hv
    rcases hv0 with hv' | hv'
    · -- between the primaries
      rw [abs_of_pos hu', abs_of_neg hv'] at hE ⊢
      set r1 := x + μ with hr1
      set r2 := -(x - 1 + μ) with hr2
      have h1 : 0 < r1 := hu'
      have h2 : 0 < r2 := by linarith
      set A := (1 - μ) / r1 ^ 2
      set B := μ / r2 ^ 2
      have hE' : -x + A - B = 0 := by
        have e1 : (1 - μ) * (r1 / r1 ^ 3) = A := by
          simp only [A]; field_simp
        have e2 : μ * ((x - 1 + μ) / r2 ^ 3) = -B := by
          simp only [B, hr2]; field_simp
        linarith
      by_cases hsmall : μ ≤ 35 / 100
      · set w : ℝ := 6 / 10 - μ
        have t1 := tan_inv r1 (6 / 10) h1 (by norm_num)
        have t2 := tan_inv r2 (4 / 10) h2 (by norm_num)
        have c1 := mul_le_mul_of_nonneg_left t1 (by linarith : (0:ℝ) ≤ 1 - μ)
        have c2 := mul_le_mul_of_nonneg_left t2 hμ0.le
        have e1 : (1 - μ) * (1 / r1 - (6 / 10 - r1) / r1 ^ 2) = (1 - μ) / r1 - (w - x) * A := by
          simp only [A, w, hr1]; field_simp; ring
        have e2 : μ * (1 / r2 - (4 / 10 - r2) / r2 ^ 2) = μ / r2 + (w - x) * B := by
          simp only [B, w, hr2]; field_simp; ring
        have e3 : (w - x) * A - (w - x) * B - x * (w - x) = 0 := by
          rw [show A = x + B by linarith]; ring
        have hsq : x ^ 2 / 2 + x * (w - x) ≤ w ^ 2 / 2 := by nlinarith [sq_nonneg (w - x)]
        have hw : w ^ 2 / 2 + (1 - μ) * (1 / (6 / 10)) + μ * (1 / (4 / 10)) ≤ 209 / 100 := by
          simp only [w]; nlinarith
        rw [e1] at c1; rw [e2] at c2
        linarith
      · push Not at hsmall
        set w : ℝ := 1 - 2 * μ
        have t1 := tan_inv r1 (1 - μ) h1 (by linarith)
        have t2 := tan_inv r2 μ h2 hμ0
        have c1 := mul_le_mul_of_nonneg_left t1 (by linarith : (0:ℝ) ≤ 1 - μ)
        have c2 := mul_le_mul_of_nonneg_left t2 hμ0.le
        have e1 : (1 - μ) * (1 / r1 - ((1 - μ) - r1) / r1 ^ 2) = (1 - μ) / r1 - (w - x) * A := by
          simp only [A, w, hr1]; field_simp; ring
        have e2 : μ * (1 / r2 - (μ - r2) / r2 ^ 2) = μ / r2 + (w - x) * B := by
          simp only [B, w, hr2]; field_simp; ring
        have e3 : (w - x) * A - (w - x) * B - x * (w - x) = 0 := by
          rw [show A = x + B by linarith]; ring
        have hsq : x ^ 2 / 2 + x * (w - x) ≤ w ^ 2 / 2 := by nlinarith [sq_nonneg (w - x)]
        have hw : w ^ 2 / 2 + (1 - μ) * (1 / (1 - μ)) + μ * (1 / μ) ≤ 209 / 100 := by
          have hm0 : (1 - μ) ≠ 0 := by linarith
          have hm1 : (1 - μ) * (1 / (1 - μ)) = 1 := by field_simp
          have hm2 : μ * (1 / μ) = 1 := by field_simp
          rw [hm1, hm2]; simp only [w]; nlinarith
        rw [e1] at c1; rw [e2] at c2
        linarith
    · -- right of the small primary
      rw [abs_of_pos hu', abs_of_pos hv'] at hE ⊢
      set r1 := x + μ with hr1
      set r2 := x - 1 + μ with hr2
      have h1 : 0 < r1 := hu'
      have h2 : 0 < r2 := hv'
      set A := (1 - μ) / r1 ^ 2
      set B := μ / r2 ^ 2
      have hE' : -x + A + B = 0 := by
        have e1 : (1 - μ) * (r1 / r1 ^ 3) = A := by
          simp only [A]; field_simp
        have e2 : μ * (r2 / r2 ^ 3) = B := by
          simp only [B]; field_simp
        linarith
      set w : ℝ := 3 / 2 - μ
      have t1 := tan_inv r1 (3 / 2) h1 (by norm_num)
      have t2 := tan_inv r2 (1 / 2) h2 (by norm_num)
      have c1 := mul_le_mul_of_nonneg_left t1 (by linarith : (0:ℝ) ≤ 1 - μ)
      have c2 := mul_le_mul_of_nonneg_left t2 hμ0.le
      have e1 : (1 - μ) * (1 / r1 - (3 / 2 - r1) / r1 ^ 2) = (1 - μ) / r1 - (w - x) * A := by
        simp only [A, w, hr1]; field_simp; ring
      have e2 : μ * (1 / r2 - (1 / 2 - r2) / r2 ^ 2) = μ / r2 - (w - x) * B := by
        simp only [B, w, hr2]; field_simp; ring
      have e3 : (w - x) * A + (w - x) * B - x * (w - x) = 0 := by
        rw [show A = x - B by linarith]; ring
      have hsq : x ^ 2 / 2 + x * (w - x) ≤ w ^ 2 / 2 := by nlinarith [sq_nonneg (w - x)]
      have hw : w ^ 2 / 2 + (1 - μ) * (1 / (3 / 2)) + μ * (1 / (1 / 2)) ≤ 209 / 100 := by
        simp only [w]; nlinarith
      rw [e1] at c1; rw [e2] at c2
      linarith

lemma offaxis_bound (μ x y R1 R2 : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 2) (hy : y ≠ 0)
    (hR1 : 0 < R1) (hR2 : 0 < R2) (hR1sq : R1 ^ 2 = (x + μ) ^ 2 + y ^ 2)
    (hR2sq : R2 ^ 2 = (x - 1 + μ) ^ 2 + y ^ 2)
    (hE0 : -x + (1 - μ) * ((x + μ) / R1 ^ 3) + μ * ((x - 1 + μ) / R2 ^ 3) = 0)
    (hE1 : -y + (1 - μ) * (y / R1 ^ 3) + μ * (y / R2 ^ 3) = 0) :
    (x ^ 2 + y ^ 2) / 2 + (1 - μ) / R1 + μ / R2 ≤ 209 / 100 := by
  set p := 1 / R1 ^ 3 with hp
  set q := 1 / R2 ^ 3 with hq
  have hp0 : 0 < p := by positivity
  have hq0 : 0 < q := by positivity
  have e0 : -x + (1 - μ) * (x + μ) * p + μ * (x - 1 + μ) * q = 0 := by
    rw [← hE0, hp, hq]; field_simp
  have e1 : y * (-1 + (1 - μ) * p + μ * q) = 0 := by
    rw [← hE1, hp, hq]; field_simp
  have hs : (1 - μ) * p + μ * q = 1 := by
    rcases mul_eq_zero.1 e1 with h | h
    · exact absurd h hy
    · linarith
  have hpq : μ * (1 - μ) * (p - q) = 0 := by
    have : -x + (1 - μ) * (x + μ) * p + μ * (x - 1 + μ) * q
        = x * ((1 - μ) * p + μ * q - 1) + μ * (1 - μ) * (p - q) := by ring
    rw [this, hs] at e0; linarith
  have hpq' : p = q := by
    have hm : μ * (1 - μ) ≠ 0 := by
      apply mul_ne_zero hμ0.ne'; linarith
    rcases mul_eq_zero.1 hpq with h | h
    · exact absurd h hm
    · linarith
  have hp1 : p = 1 := by rw [← hpq'] at hs; linarith
  have hq1 : q = 1 := by rw [← hpq']; exact hp1
  have hR1c : R1 ^ 3 = 1 := by
    have : 1 / R1 ^ 3 = 1 := hp1
    field_simp at this; linarith
  have hR2c : R2 ^ 3 = 1 := by
    have : 1 / R2 ^ 3 = 1 := hq1
    field_simp at this; linarith
  have hR1e : R1 = 1 := by
    have hf : (R1 - 1) * (R1 ^ 2 + R1 + 1) = 0 := by
      have : (R1 - 1) * (R1 ^ 2 + R1 + 1) = R1 ^ 3 - 1 := by ring
      rw [this, hR1c]; ring
    rcases mul_eq_zero.1 hf with h | h
    · linarith
    · nlinarith
  have hR2e : R2 = 1 := by
    have hf : (R2 - 1) * (R2 ^ 2 + R2 + 1) = 0 := by
      have : (R2 - 1) * (R2 ^ 2 + R2 + 1) = R2 ^ 3 - 1 := by ring
      rw [this, hR2c]; ring
    rcases mul_eq_zero.1 hf with h | h
    · linarith
    · nlinarith
  subst hR1e; subst hR2e
  have hx : x = 1 / 2 - μ := by nlinarith
  subst hx
  nlinarith

theorem _root_.solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμhalf : μ ≤ 1 / 2) (hc : 21 / 10 ≤ c) :
    belowFirstCriticalValue μ c := by
  unfold belowFirstCriticalValue firstCriticalValue
  by_cases hne : (criticalValueSet μ).Nonempty
  · have hlb : ∀ e ∈ criticalValueSet μ, -(209 / 100 : ℝ) ≤ e := by
      rintro e ⟨s, hcf, hcp, rfl⟩
      obtain ⟨h2, h3, hE0, hE1⟩ := crit_eqs μ s hcf hcp
      have hval : jacobiHamiltonian μ s = -((s 0 ^ 2 + s 1 ^ 2) / 2
          + (1 - μ) / Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)
          + μ / Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2)) := by
        simp only [jacobiHamiltonian]; rw [h2, h3]; ring
      rw [hval]
      suffices h : (s 0 ^ 2 + s 1 ^ 2) / 2 + (1 - μ) / Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)
          + μ / Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2) ≤ 209 / 100 by linarith
      obtain ⟨ha, hb⟩ := hcf
      by_cases hy : s 1 = 0
      · rw [hy] at hE0 ha hb ⊢
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
          Real.sqrt_sq_eq_abs] at hE0 ha hb ⊢
        have hu : s 0 + μ ≠ 0 := by
          intro h; rw [h] at ha; simp at ha
        have hv : s 0 - 1 + μ ≠ 0 := by
          intro h; rw [h] at hb; simp at hb
        have := axis_bound μ (s 0) hμ0 hμhalf hu hv (by linarith)
        simpa using this
      · have hR1 := Real.sqrt_pos.2 ha
        have hR2 := Real.sqrt_pos.2 hb
        have e1 : Real.sqrt (s 1 ^ 2 + (s 0 + μ) ^ 2) = Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2) := by
          rw [add_comm]
        have e2 : Real.sqrt (s 1 ^ 2 + (s 0 - 1 + μ) ^ 2)
            = Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2) := by rw [add_comm]
        rw [e1, e2, h2] at hE1
        rw [h3] at hE0
        exact offaxis_bound μ (s 0) (s 1) _ _ hμ0 hμhalf hy hR1 hR2
          (Real.sq_sqrt ha.le) (Real.sq_sqrt hb.le) (by linarith) hE1
    have := le_csInf hne hlb
    linarith
  · rw [Set.not_nonempty_iff_eq_empty.1 hne, Real.sInf_empty]
    linarith

end BirkhoffGlobalSection
