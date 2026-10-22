-- Prove2me | solution 1 for BirkhoffGlobalSection.first_critical_value_identification
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:11:01.829427+00:00
-- url     : https://prove2.me/submissions/eb753186-d5c6-44a5-8d9c-d57e8d9b3912

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


/-- directional derivatives of the Jacobi Hamiltonian at a collision-free point -/
lemma hasDer2 (μ : ℝ) (s : Phase) :
    HasDerivAt (fun t : ℝ => jacobiHamiltonian μ (s + t • coordinateVector 2)) (s 2 - s 1) 0 := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  have key := HasDerivAt.sub (HasDerivAt.div_const
      (HasDerivAt.add_const (s 3 ^ 2) (HasDerivAt.pow (HasDerivAt.const_add (s 2) hid) 2)) 2)
    (HasDerivAt.const_mul (s 1) (HasDerivAt.const_add (s 2) hid))
  exact HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq
      (HasDerivAt.add_const (s 0 * s 3 - (1 - μ) / Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)
          - μ / Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2)) key)
      (Filter.Eventually.of_forall fun t => by
        simp [jacobiHamiltonian, coordinateVector]; ring)) (by simp)

lemma hasDer3 (μ : ℝ) (s : Phase) :
    HasDerivAt (fun t : ℝ => jacobiHamiltonian μ (s + t • coordinateVector 3)) (s 3 + s 0) 0 := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  have key := HasDerivAt.add (HasDerivAt.div_const
      (HasDerivAt.const_add (s 2 ^ 2) (HasDerivAt.pow (HasDerivAt.const_add (s 3) hid) 2)) 2)
    (HasDerivAt.const_mul (s 0) (HasDerivAt.const_add (s 3) hid))
  exact HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq
      (HasDerivAt.add_const (- s 1 * s 2 - (1 - μ) / Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)
          - μ / Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2)) key)
      (Filter.Eventually.of_forall fun t => by
        simp [jacobiHamiltonian, coordinateVector]; ring)) (by simp)

lemma hasDer0 (μ : ℝ) (s : Phase) (hcf : collisionFree μ s) :
    HasDerivAt (fun t : ℝ => jacobiHamiltonian μ (s + t • coordinateVector 0))
      (s 3 + (1 - μ) * ((s 0 + μ) / (Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)) ^ 3)
        + μ * ((s 0 - 1 + μ) / (Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2)) ^ 3)) 0 := by
  obtain ⟨ha, hb⟩ := hcf
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  have hA := hasDerivAt_invsqrt (s 0 + μ) (s 1 ^ 2) ha
  have hB := hasDerivAt_invsqrt (s 0 - 1 + μ) (s 1 ^ 2) hb
  have key := HasDerivAt.sub (HasDerivAt.sub
    (HasDerivAt.mul_const (HasDerivAt.const_add (s 0) hid) (s 3))
    (HasDerivAt.const_mul (1 - μ) hA)) (HasDerivAt.const_mul μ hB)
  exact HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq
      (HasDerivAt.add_const ((s 2 ^ 2 + s 3 ^ 2) / 2 - s 1 * s 2) key)
      (Filter.Eventually.of_forall fun t => by
        simp [jacobiHamiltonian, coordinateVector, div_eq_mul_inv]; ring_nf))
      (by simp)

lemma hasDer1 (μ : ℝ) (s : Phase) (hcf : collisionFree μ s) :
    HasDerivAt (fun t : ℝ => jacobiHamiltonian μ (s + t • coordinateVector 1))
      (- s 2 + (1 - μ) * (s 1 / (Real.sqrt ((s 1) ^ 2 + (s 0 + μ) ^ 2)) ^ 3)
        + μ * (s 1 / (Real.sqrt ((s 1) ^ 2 + (s 0 - 1 + μ) ^ 2)) ^ 3)) 0 := by
  obtain ⟨ha, hb⟩ := hcf
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  have ha' : 0 < s 1 ^ 2 + (s 0 + μ) ^ 2 := by linarith
  have hb' : 0 < s 1 ^ 2 + (s 0 - 1 + μ) ^ 2 := by linarith
  have hA := hasDerivAt_invsqrt (s 1) ((s 0 + μ) ^ 2) ha'
  have hB := hasDerivAt_invsqrt (s 1) ((s 0 - 1 + μ) ^ 2) hb'
  have key := HasDerivAt.add (HasDerivAt.add
    (HasDerivAt.mul_const (HasDerivAt.const_add (s 1) hid) (s 2))
    (HasDerivAt.const_mul (1 - μ) hA)) (HasDerivAt.const_mul μ hB)
  exact HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq
      (HasDerivAt.const_sub ((s 2 ^ 2 + s 3 ^ 2) / 2 + s 0 * s 3) key)
      (Filter.Eventually.of_forall fun t => by
        simp [jacobiHamiltonian, coordinateVector, div_eq_mul_inv]; ring_nf))
      (by simp; ring)

lemma crit_eqs (μ : ℝ) (s : Phase) (hcf : collisionFree μ s)
    (hc : isCriticalPoint (jacobiHamiltonian μ) s) :
    s 2 = s 1 ∧ s 3 = - s 0 ∧
    s 3 + (1 - μ) * ((s 0 + μ) / (Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)) ^ 3)
        + μ * ((s 0 - 1 + μ) / (Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2)) ^ 3) = 0 ∧
    - s 2 + (1 - μ) * (s 1 / (Real.sqrt ((s 1) ^ 2 + (s 0 + μ) ^ 2)) ^ 3)
        + μ * (s 1 / (Real.sqrt ((s 1) ^ 2 + (s 0 - 1 + μ) ^ 2)) ^ 3) = 0 := by
  refine ⟨?_, ?_, dir_zero hc _ (hasDer0 μ s hcf), dir_zero hc _ (hasDer1 μ s hcf)⟩
  · have := dir_zero hc _ (hasDer2 μ s); linarith
  · have := dir_zero hc _ (hasDer3 μ s); linarith

lemma fderiv_dir {F : Phase → ℝ} {s : Phase} (hd : DifferentiableAt ℝ F s) (v : Phase)
    {D : ℝ} (hD : HasDerivAt (fun t : ℝ => F (s + t • v)) D 0) : fderiv ℝ F s v = D := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 0 := hasDerivAt_id 0
  have hline : HasDerivAt (fun t : ℝ => s + t • v) v 0 := by
    have := HasDerivAt.const_add s (HasDerivAt.smul_const hid v)
    simpa using this
  have h2 : HasDerivAt (fun t : ℝ => F (s + t • v)) (fderiv ℝ F s v) 0 := by
    have := HasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hd.hasFDerivAt hline (by simp)
    simpa [Function.comp_def] using this
  exact HasDerivAt.unique h2 hD

lemma clm_eq_zero (L : Phase →L[ℝ] ℝ) (h : ∀ i, L (coordinateVector i) = 0) : L = 0 := by
  ext v
  have hv : v = ∑ i, v i • coordinateVector i := by
    funext j; simp [coordinateVector, Finset.sum_apply]
  rw [hv, map_sum]
  simp [h]

lemma diff_H (μ : ℝ) (s : Phase) (hcf : collisionFree μ s) :
    DifferentiableAt ℝ (jacobiHamiltonian μ) s := by
  obtain ⟨ha, hb⟩ := hcf
  have hsa : Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hsb : Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2) ≠ 0 := (Real.sqrt_pos.2 hb).ne'
  unfold jacobiHamiltonian
  fun_prop (disch := first | exact ha.ne' | exact hb.ne' | exact hsa | exact hsb)

lemma tan_inv (r r' : ℝ) (hr : 0 < r) (hr' : 0 < r') : 1 / r - (r' - r) / r ^ 2 ≤ 1 / r' := by
  have h : 1 / r' - (1 / r - (r' - r) / r ^ 2) = (r' - r) ^ 2 / (r ^ 2 * r') := by
    field_simp; ring
  have : 0 ≤ (r' - r) ^ 2 / (r ^ 2 * r') := by positivity
  linarith

lemma seg_min (μ x w : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hx1 : 0 < x + μ) (hx2 : x - 1 + μ < 0) (hw1 : 0 < w + μ) (hw2 : w - 1 + μ < 0)
    (hE : -x + (1 - μ) * ((x + μ) / |x + μ| ^ 3) + μ * ((x - 1 + μ) / |x - 1 + μ| ^ 3) = 0) :
    x ^ 2 / 2 + (1 - μ) / |x + μ| + μ / |x - 1 + μ| ≤
      w ^ 2 / 2 + (1 - μ) / |w + μ| + μ / |w - 1 + μ| := by
  rw [abs_of_pos hx1, abs_of_neg hx2] at hE ⊢
  rw [abs_of_pos hw1, abs_of_neg hw2]
  have h1 : 0 < x + μ := hx1
  have h2 : 0 < -(x - 1 + μ) := by linarith
  have hE' : -x + (1 - μ) / (x + μ) ^ 2 - μ / (-(x - 1 + μ)) ^ 2 = 0 := by
    have e1 : (1 - μ) * ((x + μ) / (x + μ) ^ 3) = (1 - μ) / (x + μ) ^ 2 := by
      field_simp
    have e2 : μ * ((x - 1 + μ) / (-(x - 1 + μ)) ^ 3) = -(μ / (-(x - 1 + μ)) ^ 2) := by
      field_simp
    linarith
  have t1 := tan_inv (x + μ) (w + μ) h1 hw1
  have t2 := tan_inv (-(x - 1 + μ)) (-(w - 1 + μ)) h2 (by linarith)
  have c1 := mul_le_mul_of_nonneg_left t1 (by linarith : (0:ℝ) ≤ 1 - μ)
  have c2 := mul_le_mul_of_nonneg_left t2 hμ0.le
  set A := (1 - μ) / (x + μ) ^ 2 with hA
  set B := μ / (-(x - 1 + μ)) ^ 2 with hB
  have e1 : (1 - μ) * (1 / (x + μ) - ((w + μ) - (x + μ)) / (x + μ) ^ 2)
      = (1 - μ) / (x + μ) - (w - x) * A := by
    rw [hA]; field_simp; ring
  have e2 : μ * (1 / (-(x - 1 + μ)) - ((-(w - 1 + μ)) - (-(x - 1 + μ))) / (-(x - 1 + μ)) ^ 2)
      = μ / (-(x - 1 + μ)) + (w - x) * B := by
    rw [hB]; field_simp; ring
  have e3 : (w - x) * A - (w - x) * B - x * (w - x) = 0 := by
    rw [show A = x + B by linarith]; ring
  have hsq : x ^ 2 / 2 + x * (w - x) ≤ w ^ 2 / 2 := by nlinarith [sq_nonneg (w - x)]
  have f1 : (1 - μ) * (1 / (w + μ)) = (1 - μ) / (w + μ) := by ring
  have f2 : μ * (1 / -(w - 1 + μ)) = μ / -(w - 1 + μ) := by ring
  rw [e1, f1] at c1; rw [e2, f2] at c2
  linarith

lemma right_min (μ x w : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hx2 : 0 < x - 1 + μ) (hw2 : 0 < w - 1 + μ)
    (hE : -x + (1 - μ) * ((x + μ) / |x + μ| ^ 3) + μ * ((x - 1 + μ) / |x - 1 + μ| ^ 3) = 0) :
    x ^ 2 / 2 + (1 - μ) / |x + μ| + μ / |x - 1 + μ| ≤
      w ^ 2 / 2 + (1 - μ) / |w + μ| + μ / |w - 1 + μ| := by
  have hx1 : 0 < x + μ := by linarith
  have hw1 : 0 < w + μ := by linarith
  rw [abs_of_pos hx1, abs_of_pos hx2] at hE ⊢
  rw [abs_of_pos hw1, abs_of_pos hw2]
  have hE' : -x + (1 - μ) / (x + μ) ^ 2 + μ / (x - 1 + μ) ^ 2 = 0 := by
    have e1 : (1 - μ) * ((x + μ) / (x + μ) ^ 3) = (1 - μ) / (x + μ) ^ 2 := by
      field_simp
    have e2 : μ * ((x - 1 + μ) / (x - 1 + μ) ^ 3) = μ / (x - 1 + μ) ^ 2 := by
      field_simp
    linarith
  have t1 := tan_inv (x + μ) (w + μ) hx1 hw1
  have t2 := tan_inv (x - 1 + μ) (w - 1 + μ) hx2 hw2
  have c1 := mul_le_mul_of_nonneg_left t1 (by linarith : (0:ℝ) ≤ 1 - μ)
  have c2 := mul_le_mul_of_nonneg_left t2 hμ0.le
  set A := (1 - μ) / (x + μ) ^ 2 with hA
  set B := μ / (x - 1 + μ) ^ 2 with hB
  have e1 : (1 - μ) * (1 / (x + μ) - ((w + μ) - (x + μ)) / (x + μ) ^ 2)
      = (1 - μ) / (x + μ) - (w - x) * A := by
    rw [hA]; field_simp; ring
  have e2 : μ * (1 / (x - 1 + μ) - ((w - 1 + μ) - (x - 1 + μ)) / (x - 1 + μ) ^ 2)
      = μ / (x - 1 + μ) - (w - x) * B := by
    rw [hB]; field_simp; ring
  have e3 : (w - x) * A + (w - x) * B - x * (w - x) = 0 := by
    rw [show A = x - B by linarith]; ring
  have hsq : x ^ 2 / 2 + x * (w - x) ≤ w ^ 2 / 2 := by nlinarith [sq_nonneg (w - x)]
  have f1 : (1 - μ) * (1 / (w + μ)) = (1 - μ) / (w + μ) := by ring
  have f2 : μ * (1 / (w - 1 + μ)) = μ / (w - 1 + μ) := by ring
  rw [e1, f1] at c1; rw [e2, f2] at c2
  linarith

lemma left_min (μ x w : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hx1 : x + μ < 0) (hw1 : w + μ < 0)
    (hE : -x + (1 - μ) * ((x + μ) / |x + μ| ^ 3) + μ * ((x - 1 + μ) / |x - 1 + μ| ^ 3) = 0) :
    x ^ 2 / 2 + (1 - μ) / |x + μ| + μ / |x - 1 + μ| ≤
      w ^ 2 / 2 + (1 - μ) / |w + μ| + μ / |w - 1 + μ| := by
  have hx2 : x - 1 + μ < 0 := by linarith
  have hw2 : w - 1 + μ < 0 := by linarith
  rw [abs_of_neg hx1, abs_of_neg hx2] at hE ⊢
  rw [abs_of_neg hw1, abs_of_neg hw2]
  have h1 : 0 < -(x + μ) := by linarith
  have h2 : 0 < -(x - 1 + μ) := by linarith
  have hE' : -x - (1 - μ) / (-(x + μ)) ^ 2 - μ / (-(x - 1 + μ)) ^ 2 = 0 := by
    have e1 : (1 - μ) * ((x + μ) / (-(x + μ)) ^ 3) = -((1 - μ) / (-(x + μ)) ^ 2) := by
      field_simp
    have e2 : μ * ((x - 1 + μ) / (-(x - 1 + μ)) ^ 3) = -(μ / (-(x - 1 + μ)) ^ 2) := by
      field_simp
    linarith
  have t1 := tan_inv (-(x + μ)) (-(w + μ)) h1 (by linarith)
  have t2 := tan_inv (-(x - 1 + μ)) (-(w - 1 + μ)) h2 (by linarith)
  have c1 := mul_le_mul_of_nonneg_left t1 (by linarith : (0:ℝ) ≤ 1 - μ)
  have c2 := mul_le_mul_of_nonneg_left t2 hμ0.le
  set A := (1 - μ) / (-(x + μ)) ^ 2 with hA
  set B := μ / (-(x - 1 + μ)) ^ 2 with hB
  have e1 : (1 - μ) * (1 / (-(x + μ)) - ((-(w + μ)) - (-(x + μ))) / (-(x + μ)) ^ 2)
      = (1 - μ) / (-(x + μ)) + (w - x) * A := by
    rw [hA]; field_simp; ring
  have e2 : μ * (1 / (-(x - 1 + μ)) - ((-(w - 1 + μ)) - (-(x - 1 + μ))) / (-(x - 1 + μ)) ^ 2)
      = μ / (-(x - 1 + μ)) + (w - x) * B := by
    rw [hB]; field_simp; ring
  have e3 : (w - x) * A + (w - x) * B + x * (w - x) = 0 := by
    rw [show A = -x - B by linarith]; ring
  have hsq : x ^ 2 / 2 + x * (w - x) ≤ w ^ 2 / 2 := by nlinarith [sq_nonneg (w - x)]
  have f1 : (1 - μ) * (1 / -(w + μ)) = (1 - μ) / -(w + μ) := by ring
  have f2 : μ * (1 / -(w - 1 + μ)) = μ / -(w - 1 + μ) := by ring
  rw [e1, f1] at c1; rw [e2, f2] at c2
  linarith

lemma key_ineq (t : ℝ) (h0 : 0 < t) (h1 : t < 1) : 1 / (1 + t) + 2 * t ≤ 1 / (1 - t) := by
  have ha : 0 < 1 + t := by linarith
  have hb : 0 < 1 - t := by linarith
  rw [div_add' _ _ _ ha.ne', div_le_div_iff₀ ha hb]
  nlinarith [pow_pos h0 3]

lemma f_ge (r : ℝ) (hr : 0 < r) : 3 / 2 ≤ r ^ 2 / 2 + 1 / r := by
  have : r ^ 2 / 2 + 1 / r - 3 / 2 = (r - 1) ^ 2 * (r + 2) / (2 * r) := by
    field_simp; ring
  have : 0 ≤ (r - 1) ^ 2 * (r + 2) / (2 * r) := by positivity
  linarith

lemma offaxis_le (μ x y R1 R2 : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hy : y ≠ 0)
    (hR1 : 0 < R1) (hR2 : 0 < R2) (hR1sq : R1 ^ 2 = (x + μ) ^ 2 + y ^ 2)
    (hR2sq : R2 ^ 2 = (x - 1 + μ) ^ 2 + y ^ 2)
    (hE0 : -x + (1 - μ) * ((x + μ) / R1 ^ 3) + μ * ((x - 1 + μ) / R2 ^ 3) = 0)
    (hE1 : -y + (1 - μ) * (y / R1 ^ 3) + μ * (y / R2 ^ 3) = 0) :
    (x ^ 2 + y ^ 2) / 2 + (1 - μ) / R1 + μ / R2 ≤ 3 / 2 - μ * (1 - μ) / 2 := by
  set p := 1 / R1 ^ 3 with hp
  set q := 1 / R2 ^ 3 with hq
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

lemma omega_x1_lower (μ x1 : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (ha : 0 < x1 + μ) (hb : x1 - 1 + μ < 0) :
    3 / 2 - μ * (1 - μ) / 2 ≤ x1 ^ 2 / 2 + (1 - μ) / |x1 + μ| + μ / |x1 - 1 + μ| := by
  rw [abs_of_pos ha, abs_of_neg hb]
  have hr2 : 0 < -(x1 - 1 + μ) := by linarith
  have k1 := mul_le_mul_of_nonneg_left (f_ge (x1 + μ) ha) (by linarith : (0:ℝ) ≤ 1 - μ)
  have k2 := mul_le_mul_of_nonneg_left (f_ge (-(x1 - 1 + μ)) hr2) hμ0.le
  have e1 : (1 - μ) * ((x1 + μ) ^ 2 / 2 + 1 / (x1 + μ))
      = (1 - μ) * (x1 + μ) ^ 2 / 2 + (1 - μ) / (x1 + μ) := by ring
  have e2 : μ * ((-(x1 - 1 + μ)) ^ 2 / 2 + 1 / (-(x1 - 1 + μ)))
      = μ * (-(x1 - 1 + μ)) ^ 2 / 2 + μ / (-(x1 - 1 + μ)) := by ring
  rw [e1] at k1; rw [e2] at k2
  have id : x1 ^ 2 = (1 - μ) * (x1 + μ) ^ 2 + μ * (-(x1 - 1 + μ)) ^ 2 - μ * (1 - μ) := by ring
  nlinarith

set_option maxHeartbeats 8000000 in
theorem _root_.solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    (criticalValueSet μ).Nonempty ∧
    BddBelow (criticalValueSet μ) ∧
    ∃ l₁ : Phase,
      IsInnerLagrangePoint μ l₁ ∧
      jacobiHamiltonian μ l₁ = firstCriticalValue μ := by
  -- the inner Lagrange point by the intermediate value theorem
  set g : ℝ → ℝ := fun x => -x + (1 - μ) / (x + μ) ^ 2 - μ / (1 - x - μ) ^ 2 with hg_def
  have hab : -μ + (1 - μ) / 3 ≤ 1 - μ - μ / 3 := by linarith
  have hcont : ContinuousOn g (Set.Icc (-μ + (1 - μ) / 3) (1 - μ - μ / 3)) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.add continuous_neg.continuousOn
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx
      have : 0 < x + μ := by linarith [hx.1]
      positivity
    · apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx
      have : 0 < 1 - x - μ := by linarith [hx.2]
      positivity
  have hga : 0 < g (-μ + (1 - μ) / 3) := by
    simp only [hg_def]
    rw [show -μ + (1 - μ) / 3 + μ = (1 - μ) / 3 by ring,
      show 1 - (-μ + (1 - μ) / 3) - μ = (2 + μ) / 3 by ring]
    have h1 : 9 ≤ (1 - μ) / ((1 - μ) / 3) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h2 : μ / ((2 + μ) / 3) ^ 2 ≤ 9 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hgb : g (1 - μ - μ / 3) < 0 := by
    simp only [hg_def]
    rw [show 1 - μ - μ / 3 + μ = 1 - μ / 3 by ring,
      show 1 - (1 - μ - μ / 3) - μ = μ / 3 by ring]
    have h1 : 9 ≤ μ / (μ / 3) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h2 : (1 - μ) / (1 - μ / 3) ^ 2 ≤ 9 / 4 := by
      rw [div_le_iff₀ (by nlinarith)]; nlinarith
    linarith
  obtain ⟨x1, hx1mem, hgx1⟩ := intermediate_value_Icc' hab hcont ⟨hgb.le, hga.le⟩
  have hx1a : 0 < x1 + μ := by linarith [hx1mem.1]
  have hx1b : x1 - 1 + μ < 0 := by linarith [hx1mem.2]
  have hg1 : -x1 + (1 - μ) / (x1 + μ) ^ 2 - μ / (1 - x1 - μ) ^ 2 = 0 := hgx1
  set l1 : Phase := ![x1, 0, 0, -x1] with hl1
  have hcf1 : collisionFree μ l1 := by
    refine ⟨?_, ?_⟩ <;> simp [hl1] <;> nlinarith
  have hd1 := diff_H μ l1 hcf1
  have d0 : fderiv ℝ (jacobiHamiltonian μ) l1 (coordinateVector 0) = 0 := by
    rw [fderiv_dir hd1 _ (hasDer0 μ l1 hcf1)]
    simp only [hl1]
    simp [Real.sqrt_sq_eq_abs, abs_of_pos hx1a, abs_of_neg hx1b]
    have e1 : (1 - μ) * ((x1 + μ) / (x1 + μ) ^ 3) = (1 - μ) / (x1 + μ) ^ 2 := by
      field_simp
    have hn : (0:ℝ) < -(x1 - 1 + μ) := by linarith
    have hn' : (-μ + (1 - x1)) ≠ 0 := by linarith
    have e2 : μ * ((x1 - 1 + μ) / (-μ + (1 - x1)) ^ 3) = -(μ / (1 - x1 - μ) ^ 2) := by
      rw [show (1 - x1 - μ) = -μ + (1 - x1) by ring]
      field_simp
      ring
    linarith
  have d1 : fderiv ℝ (jacobiHamiltonian μ) l1 (coordinateVector 1) = 0 := by
    rw [fderiv_dir hd1 _ (hasDer1 μ l1 hcf1)]
    simp [hl1]
  have d2 : fderiv ℝ (jacobiHamiltonian μ) l1 (coordinateVector 2) = 0 := by
    rw [fderiv_dir hd1 _ (hasDer2 μ l1)]
    simp [hl1]
  have d3 : fderiv ℝ (jacobiHamiltonian μ) l1 (coordinateVector 3) = 0 := by
    rw [fderiv_dir hd1 _ (hasDer3 μ l1)]
    simp [hl1]
  have hcp1 : isCriticalPoint (jacobiHamiltonian μ) l1 := by
    refine ⟨hd1, clm_eq_zero _ ?_⟩
    intro i
    fin_cases i
    · exact d0
    · exact d1
    · exact d2
    · exact d3
  have hIL : IsInnerLagrangePoint μ l1 := by
    refine ⟨hcf1, hcp1, ?_, ?_, ?_⟩ <;> simp [hl1] <;> linarith
  have hval1 : jacobiHamiltonian μ l1 =
      -(x1 ^ 2 / 2 + (1 - μ) / |x1 + μ| + μ / |x1 - 1 + μ|) := by
    simp [jacobiHamiltonian, hl1, Real.sqrt_sq_eq_abs]
    ring
  have hlow := omega_x1_lower μ x1 hμ0 hμ1 hx1a hx1b
  have hmin : ∀ e ∈ criticalValueSet μ, jacobiHamiltonian μ l1 ≤ e := by
    rintro e ⟨s, hcf, hcp, rfl⟩
    obtain ⟨h2, h3, hE0, hE1⟩ := crit_eqs μ s hcf hcp
    have hval : jacobiHamiltonian μ s = -((s 0 ^ 2 + s 1 ^ 2) / 2
        + (1 - μ) / Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)
        + μ / Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2)) := by
      simp only [jacobiHamiltonian]; rw [h2, h3]; ring
    rw [hval, hval1]
    suffices h : (s 0 ^ 2 + s 1 ^ 2) / 2 + (1 - μ) / Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2)
        + μ / Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2) ≤
        x1 ^ 2 / 2 + (1 - μ) / |x1 + μ| + μ / |x1 - 1 + μ| by linarith
    obtain ⟨ha, hb⟩ := hcf
    by_cases hy : s 1 = 0
    · rw [hy] at hE0 ha hb ⊢
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
        Real.sqrt_sq_eq_abs] at hE0 ha hb ⊢
      have hu : s 0 + μ ≠ 0 := by
        intro h; rw [h] at ha; simp at ha
      have hv : s 0 - 1 + μ ≠ 0 := by
        intro h; rw [h] at hb; simp at hb
      have hE : -(s 0) + (1 - μ) * ((s 0 + μ) / |s 0 + μ| ^ 3)
          + μ * ((s 0 - 1 + μ) / |s 0 - 1 + μ| ^ 3) = 0 := by linarith
      have hgoal : s 0 ^ 2 / 2 + (1 - μ) / |s 0 + μ| + μ / |s 0 - 1 + μ| ≤
          x1 ^ 2 / 2 + (1 - μ) / |x1 + μ| + μ / |x1 - 1 + μ| := by
        rcases lt_or_gt_of_ne hu with hu' | hu'
        · -- left of the large primary
          have hw := left_min μ (s 0) (-2 * μ - x1) hμ0 hμ1 hu' (by linarith) hE
          have hρ1 : 0 < x1 + μ := hx1a
          have hρ2 : x1 + μ < 1 := by linarith
          have k := mul_le_mul_of_nonneg_left (key_ineq (x1 + μ) hρ1 hρ2) hμ0.le
          rw [abs_of_neg (by linarith : -2 * μ - x1 + μ < 0),
            abs_of_neg (by linarith : -2 * μ - x1 - 1 + μ < 0)] at hw
          rw [abs_of_pos hx1a, abs_of_neg hx1b]
          have c1 : -(-2 * μ - x1 + μ) = x1 + μ := by ring
          have c2 : -(-2 * μ - x1 - 1 + μ) = 1 + (x1 + μ) := by ring
          have c3 : -(x1 - 1 + μ) = 1 - (x1 + μ) := by ring
          rw [c1, c2] at hw; rw [c3]
          have e1 : μ * (1 / (1 + (x1 + μ)) + 2 * (x1 + μ))
              = μ / (1 + (x1 + μ)) + 2 * μ * (x1 + μ) := by ring
          have e2 : μ * (1 / (1 - (x1 + μ))) = μ / (1 - (x1 + μ)) := by ring
          rw [e1, e2] at k
          have hw2 : (-2 * μ - x1) ^ 2 / 2 = x1 ^ 2 / 2 + 2 * μ * (x1 + μ) := by ring
          linarith
        · rcases lt_or_gt_of_ne hv with hv' | hv'
          · exact seg_min μ (s 0) x1 hμ0 hμ1 hu' hv' hx1a hx1b hE
          · -- right of the small primary
            have hw := right_min μ (s 0) (2 - 2 * μ - x1) hμ0 hμ1 hv' (by linarith) hE
            have ht1 : 0 < 1 - μ - x1 := by linarith
            have ht2 : 1 - μ - x1 < 1 := by linarith
            have k := mul_le_mul_of_nonneg_left (key_ineq (1 - μ - x1) ht1 ht2)
              (by linarith : (0:ℝ) ≤ 1 - μ)
            rw [abs_of_pos (by linarith : 0 < 2 - 2 * μ - x1 + μ),
              abs_of_pos (by linarith : 0 < 2 - 2 * μ - x1 - 1 + μ)] at hw
            rw [abs_of_pos hx1a, abs_of_neg hx1b]
            have c1 : 2 - 2 * μ - x1 + μ = 1 + (1 - μ - x1) := by ring
            have c2 : 2 - 2 * μ - x1 - 1 + μ = 1 - μ - x1 := by ring
            have c3 : -(x1 - 1 + μ) = 1 - μ - x1 := by ring
            have c4 : x1 + μ = 1 - (1 - μ - x1) := by ring
            rw [c1, c2] at hw; rw [c3, c4]
            have e1 : (1 - μ) * (1 / (1 + (1 - μ - x1)) + 2 * (1 - μ - x1))
                = (1 - μ) / (1 + (1 - μ - x1)) + 2 * (1 - μ) * (1 - μ - x1) := by ring
            have e2 : (1 - μ) * (1 / (1 - (1 - μ - x1))) = (1 - μ) / (1 - (1 - μ - x1)) := by
              ring
            rw [e1, e2] at k
            have hw2 : (2 - 2 * μ - x1) ^ 2 / 2 = x1 ^ 2 / 2 + 2 * (1 - μ) * (1 - μ - x1) := by
              ring
            linarith
      simpa using hgoal
    · have hR1 := Real.sqrt_pos.2 ha
      have hR2 := Real.sqrt_pos.2 hb
      have e1 : Real.sqrt (s 1 ^ 2 + (s 0 + μ) ^ 2) = Real.sqrt ((s 0 + μ) ^ 2 + s 1 ^ 2) := by
        rw [add_comm]
      have e2 : Real.sqrt (s 1 ^ 2 + (s 0 - 1 + μ) ^ 2)
          = Real.sqrt ((s 0 - 1 + μ) ^ 2 + s 1 ^ 2) := by rw [add_comm]
      rw [e1, e2, h2] at hE1
      rw [h3] at hE0
      have := offaxis_le μ (s 0) (s 1) _ _ hμ0 hμ1 hy hR1 hR2
        (Real.sq_sqrt ha.le) (Real.sq_sqrt hb.le) (by linarith) hE1
      linarith
  have hmem : jacobiHamiltonian μ l1 ∈ criticalValueSet μ := ⟨l1, hcf1, hcp1, rfl⟩
  have hleast : IsLeast (criticalValueSet μ) (jacobiHamiltonian μ l1) := ⟨hmem, hmin⟩
  refine ⟨⟨_, hmem⟩, ⟨_, hmin⟩, l1, hIL, ?_⟩
  unfold firstCriticalValue
  exact hleast.csInf_eq.symm

end BirkhoffGlobalSection

