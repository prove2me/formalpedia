-- Prove2me | solution 2 for DiazModulus.period_free_split_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:37:03.155071+00:00
-- url     : https://prove2.me/submissions/afdf1f9e-228c-4274-b88c-aafc8d4eaaed

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_pi_transcendental
import Theorems.Thm_Transcendence_quadratic_coeffs_eq_zero_of_transcendental

/-!
# Both halves of the period-free region are non-empty

Consider the `u ∈ ℂ` with `u ≠ 0`, `|u|` algebraic, `exp u` not real, `Re u ≠ 0 ≠ Im u`,
`Im u` not a rational multiple of `π`, and `π (Im u + r π)` transcendental for every rational
`r ≠ 0`. Whether `π · Im u` is algebraic splits them in two, and each half contains a point of
modulus `4`:

* `wC = √(16 − 1/π²) + i/π`, where `π · Im wC = 1` is algebraic;
* `wB = √15 + i`, where `π · Im wB = π` is transcendental.

The only transcendence input is that of `π`. Apart from `π · Im wB = π` itself, it is used in
one form: if `c₂ π² + c₁ π + c₀ = 0` with `c₀, c₁, c₂` algebraic, then `c₂ = c₁ = c₀ = 0`.
-/

namespace S7W2_period_free_split_nondegenerate

open Complex ComplexConjugate

theorem alg_rat (q : ℚ) : IsAlgebraic ℚ ((q : ℂ)) := by
  simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) q)

/-- `Im (exp u) = e^{Re u} sin (Im u)` vanishes only when `Im u ∈ π ℤ`, so `exp u` is not real
as soon as `Im u` is not a rational multiple of `π`. -/
theorem exp_im_ne_zero_of_not_pi_rat {u : ℂ}
    (h : ¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) : (Complex.exp u).im ≠ 0 := by
  intro hc
  have h' := Complex.exp_im u
  rw [hc] at h'
  have hs : Real.sin u.im = 0 := by
    rcases mul_eq_zero.1 h'.symm with h1 | h1
    · exact absurd h1 (Real.exp_ne_zero _)
    · exact h1
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hs
  exact h ⟨(n : ℚ), by push_cast; exact hn.symm⟩

/-! ## The algebraic half: `wC = √(16 − 1/π²) + i/π` -/

noncomputable def yC : ℝ := 1 / Real.pi

noncomputable def wC : ℂ := ⟨Real.sqrt (16 - yC ^ 2), yC⟩

/-- `0 < 1/π < 1/3`, so `(1/π)² < 16`. -/
theorem yC_sq_lt : yC ^ 2 < 16 := by
  have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h0 : 0 < yC := by unfold yC; positivity
  have h1 : yC < 1 / 3 := by
    unfold yC
    rw [div_lt_div_iff₀ hpos (by norm_num)]
    linarith [Real.pi_gt_three]
  nlinarith [h0, h1]

theorem norm_wC : ‖wC‖ = 4 := by
  have h1 : (0 : ℝ) ≤ 16 - yC ^ 2 := by linarith [yC_sq_lt]
  have h2 : Complex.normSq wC = 16 := by
    rw [wC, Complex.normSq_mk, Real.mul_self_sqrt h1]; ring
  have h3 : ‖wC‖ ^ 2 = 16 := by rw [← Complex.normSq_eq_norm_sq, h2]
  nlinarith [norm_nonneg wC, h3]

theorem wC_re_pos : 0 < wC.re := by
  have h1 : (0 : ℝ) < 16 - yC ^ 2 := by linarith [yC_sq_lt]
  simpa [wC] using Real.sqrt_pos.2 h1

theorem wC_im : wC.im = 1 / Real.pi := rfl

/-- `1/π = q π` would give `q π² + 0 · π − 1 = 0`, a relation whose constant term is not `0`. -/
theorem wC_not_pi_rat (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) :
    ¬ ∃ q : ℚ, wC.im = (q : ℝ) * Real.pi := by
  rintro ⟨q, hq⟩
  have hy : (1 / Real.pi : ℝ) = (q : ℝ) * Real.pi := by rw [← wC_im]; exact hq
  have h1 : (1 / Real.pi) * Real.pi = 1 := by field_simp
  have hmul : (1 / Real.pi) * Real.pi = ((q : ℝ) * Real.pi) * Real.pi := by rw [hy]
  have hkey : (q : ℝ) * Real.pi ^ 2 = 1 := by nlinarith [hmul, h1]
  have hrel : (q : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 + 0 * ((Real.pi : ℝ) : ℂ) + -1 = 0 := by
    have hcast : ((((q : ℝ)) * Real.pi ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [hkey]
    push_cast at hcast
    linear_combination hcast
  have h := (Transcendence.quadratic_coeffs_eq_zero_of_transcendental hpi
    (isAlgebraic_one (R := ℚ) (A := ℂ)).neg isAlgebraic_zero (alg_rat q) hrel).2.2
  norm_num at h

/-- `wC` lies in the half where `π · Im u` is algebraic. -/
theorem wC_mem (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) :
    wC ≠ 0 ∧ IsAlgebraic ℚ ((‖wC‖ : ℝ) : ℂ) ∧ (Complex.exp wC).im ≠ 0 ∧
      ¬ (wC.im = 0 ∨ wC.re = 0) ∧ (¬ ∃ q : ℚ, wC.im = (q : ℝ) * Real.pi) ∧
      (¬ ∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (wC.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) ∧
      IsAlgebraic ℚ ((Real.pi * wC.im : ℝ) : ℂ) := by
  have hre : wC.re ≠ 0 := ne_of_gt wC_re_pos
  have him : wC.im ≠ 0 := by rw [wC_im]; positivity
  have hpiim : IsAlgebraic ℚ ((Real.pi * wC.im : ℝ) : ℂ) := by
    have h1 : (Real.pi * wC.im : ℝ) = 1 := by rw [wC_im]; field_simp
    rw [h1]
    have : (((1 : ℝ)) : ℂ) = ((1 : ℚ) : ℂ) := by push_cast; ring
    rw [this]; exact alg_rat _
  refine ⟨?_, ?_, exp_im_ne_zero_of_not_pi_rat (wC_not_pi_rat hpi), ?_,
    wC_not_pi_rat hpi, ?_, hpiim⟩
  · intro h; exact hre (by rw [h]; rfl)
  · rw [norm_wC]
    have : (((4 : ℝ)) : ℂ) = ((4 : ℚ) : ℂ) := by push_cast; ring
    rw [this]; exact alg_rat _
  · rintro (h | h)
    · exact him h
    · exact hre h
  · -- `r π² + 0 · π + (π Im wC − π (Im wC + r π)) = 0` has algebraic coefficients, so `r = 0`.
    rintro ⟨r, hr0, halg⟩
    have h := (Transcendence.quadratic_coeffs_eq_zero_of_transcendental hpi (hpiim.sub halg)
      isAlgebraic_zero (alg_rat r) (by push_cast; ring)).1
    exact hr0 (by exact_mod_cast h)

/-! ## The transcendental half: `wB = √15 + i` -/

noncomputable def wB : ℂ := ⟨Real.sqrt 15, 1⟩

theorem norm_wB : ‖wB‖ = 4 := by
  have h2 : Complex.normSq wB = 16 := by
    rw [wB, Complex.normSq_mk, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 15)]; ring
  have h3 : ‖wB‖ ^ 2 = 16 := by rw [← Complex.normSq_eq_norm_sq, h2]
  nlinarith [norm_nonneg wB, h3]

/-- `1 = q π` would give `0 · π² + q π − 1 = 0`, a relation whose constant term is not `0`. -/
theorem wB_not_pi_rat (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) :
    ¬ ∃ q : ℚ, wB.im = (q : ℝ) * Real.pi := by
  rintro ⟨q, hq⟩
  have hy : (1 : ℝ) = (q : ℝ) * Real.pi := hq
  have hrel : (0 : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 + (q : ℂ) * ((Real.pi : ℝ) : ℂ) + -1 = 0 := by
    have hcast : ((1 : ℝ) : ℂ) = (((q : ℝ) * Real.pi : ℝ) : ℂ) := by rw [hy]
    push_cast at hcast
    linear_combination -hcast
  have h := (Transcendence.quadratic_coeffs_eq_zero_of_transcendental hpi
    (isAlgebraic_one (R := ℚ) (A := ℂ)).neg (alg_rat q) isAlgebraic_zero hrel).2.2
  norm_num at h

/-- `wB` lies in the half where `π · Im u` is transcendental. -/
theorem wB_mem (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) :
    wB ≠ 0 ∧ IsAlgebraic ℚ ((‖wB‖ : ℝ) : ℂ) ∧ (Complex.exp wB).im ≠ 0 ∧
      ¬ (wB.im = 0 ∨ wB.re = 0) ∧ (¬ ∃ q : ℚ, wB.im = (q : ℝ) * Real.pi) ∧
      (¬ ∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (wB.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) ∧
      Transcendental ℚ ((Real.pi * wB.im : ℝ) : ℂ) := by
  have hb : wB.im = 1 := rfl
  have hre : wB.re ≠ 0 := by
    have : wB.re = Real.sqrt 15 := rfl
    rw [this]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have him : wB.im ≠ 0 := by rw [hb]; norm_num
  refine ⟨?_, ?_, exp_im_ne_zero_of_not_pi_rat (wB_not_pi_rat hpi), ?_,
    wB_not_pi_rat hpi, ?_, ?_⟩
  · intro h; exact hre (by rw [h]; rfl)
  · rw [norm_wB]
    have : (((4 : ℝ)) : ℂ) = ((4 : ℚ) : ℂ) := by push_cast; ring
    rw [this]; exact alg_rat _
  · rintro (h | h)
    · exact him h
    · exact hre h
  · -- `r π² + 1 · π − π (Im wB + r π) = 0` has algebraic coefficients, so `r = 0`.
    rintro ⟨r, hr0, halg⟩
    have h := (Transcendence.quadratic_coeffs_eq_zero_of_transcendental hpi halg.neg
      isAlgebraic_one (alg_rat r) (by rw [hb]; push_cast; ring)).1
    exact hr0 (by exact_mod_cast h)
  · -- `π · Im wB = π`.
    intro hpa
    refine hpi ?_
    have hz : ((Real.pi * wB.im : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) := by
      rw [hb]; push_cast; ring
    rw [hz] at hpa
    exact hpa

end S7W2_period_free_split_nondegenerate

/- `wC` witnesses the first half and `wB` the second; both use only that `π` is
transcendental. -/
open Complex ComplexConjugate in
theorem solution :
    (∃ u : ℂ, u ≠ 0 ∧ IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) ∧ (Complex.exp u).im ≠ 0 ∧
        ¬ (u.im = 0 ∨ u.re = 0) ∧ (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) ∧
        (¬ ∃ r : ℚ, r ≠ 0 ∧
          IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) ∧
        IsAlgebraic ℚ ((Real.pi * u.im : ℝ) : ℂ)) ∧
    (∃ u : ℂ, u ≠ 0 ∧ IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) ∧ (Complex.exp u).im ≠ 0 ∧
        ¬ (u.im = 0 ∨ u.re = 0) ∧ (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) ∧
        (¬ ∃ r : ℚ, r ≠ 0 ∧
          IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) ∧
        Transcendental ℚ ((Real.pi * u.im : ℝ) : ℂ)) := by
  have hpi := DiazModulus.pi_transcendental
  exact ⟨⟨_, S7W2_period_free_split_nondegenerate.wC_mem hpi⟩,
    ⟨_, S7W2_period_free_split_nondegenerate.wB_mem hpi⟩⟩

#print axioms solution
