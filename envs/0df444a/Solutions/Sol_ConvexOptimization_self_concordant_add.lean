-- Prove2me | solution 1 for ConvexOptimization.self_concordant_add
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-15T14:40:36.053149+00:00
-- url     : https://prove2.me/submissions/06caf029-ecd2-4049-83b5-c0aa551721f5

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace SCAddAux

/-- `a ^ (3/2) = a * √a` for `a ≥ 0`. -/
theorem rpow_three_halves {a : ℝ} (ha : 0 ≤ a) : a ^ ((3 : ℝ) / 2) = a * Real.sqrt a := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add' ha (by norm_num),
    Real.rpow_one, Real.sqrt_eq_rpow]

/-- Superadditivity of `t ↦ t ^ (3/2)` on the nonnegative reals: this is the
elementary inequality `2(a^{3/2} + b^{3/2}) ≤ 2(a+b)^{3/2}` behind B&V's proof. -/
theorem rpow_three_halves_superadditive {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ ((3 : ℝ) / 2) + b ^ ((3 : ℝ) / 2) ≤ (a + b) ^ ((3 : ℝ) / 2) := by
  rw [rpow_three_halves ha, rpow_three_halves hb, rpow_three_halves (by linarith)]
  have h1 : Real.sqrt a ≤ Real.sqrt (a + b) := Real.sqrt_le_sqrt (by linarith)
  have h2 : Real.sqrt b ≤ Real.sqrt (a + b) := Real.sqrt_le_sqrt (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

/-- Along every line through a point of the (open) domain, a convex `C³` function has
nonnegative second derivative. This is what makes the right-hand side of the
self-concordance inequality a genuine `3/2` power of a nonnegative number. -/
theorem line_second_deriv_nonneg {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩo : IsOpen Ω) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ Ω f)
    (hcd : ContDiffOn ℝ 3 f Ω) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Ω)
    (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 := by
  have hℓ : ContDiff ℝ (3 : ℕ) (fun t : ℝ => x + t • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  set T : Set ℝ := {t : ℝ | x + t • v ∈ Ω} with hTdef
  have hTopen : IsOpen T := hΩo.preimage hℓ.continuous
  have h0T : (0 : ℝ) ∈ T := by simpa [hTdef] using hx
  -- The line parameter set is convex, and the restriction of `f` to the line is convex.
  have hcomb : ∀ p q s t : ℝ, s + t = 1 →
      s • (x + p • v) + t • (x + q • v) = x + (s * p + t * q) • v := by
    intro p q s t hst
    match_scalars
    · linear_combination hst
    · ring
  have hTconv : Convex ℝ T := by
    intro p hp q hq s t hs ht hst
    have hmem := hconv.1 hp hq hs ht hst
    rwa [hcomb p q s t hst] at hmem
  have hφconv : ConvexOn ℝ T (fun t : ℝ => f (x + t • v)) := by
    refine ⟨hTconv, fun p hp q hq s t hs ht hst => ?_⟩
    have := hconv.2 hp hq hs ht hst
    rwa [hcomb p q s t hst] at this
  -- Differentiability of the restriction on `T`.
  have hdiff : ∀ t ∈ T, DifferentiableAt ℝ (fun t : ℝ => f (x + t • v)) t := by
    intro t ht
    have hfa : ContDiffAt ℝ (3 : ℕ) f ((fun t : ℝ => x + t • v) t) :=
      hcd.contDiffAt (hΩo.mem_nhds ht)
    have : ContDiffAt ℝ (3 : ℕ) (fun t : ℝ => f (x + t • v)) t := by
      simpa [Function.comp_def] using hfa.comp t hℓ.contDiffAt
    exact this.differentiableAt (by norm_num)
  -- Convexity makes the first derivative monotone; hence the second derivative is `≥ 0`.
  have hmono : MonotoneOn (deriv fun t : ℝ => f (x + t • v)) T := hφconv.monotoneOn_deriv hdiff
  have hnn : 0 ≤ derivWithin (deriv fun t : ℝ => f (x + t • v)) T 0 := hmono.derivWithin_nonneg
  rw [derivWithin_of_isOpen hTopen h0T] at hnn
  rwa [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]

end SCAddAux

open ConvexOptimization in
theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩo : IsOpen Ω) (f h : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsSelfConcordantOn Ω f) (hh : IsSelfConcordantOn Ω h) :
    IsSelfConcordantOn Ω (f + h) := by
  obtain ⟨hfc, hfd, hfi⟩ := hf
  obtain ⟨hhc, hhd, hhi⟩ := hh
  refine ⟨hfc.add hhc, hfd.add hhd, ?_⟩
  intro x hx v
  -- Restrictions to the line `t ↦ x + t • v` are `C³` at `0`.
  have hℓ : ContDiff ℝ (3 : ℕ) (fun t : ℝ => x + t • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hrestrict : ∀ p : EuclideanSpace ℝ (Fin n) → ℝ, ContDiffOn ℝ 3 p Ω →
      ContDiffAt ℝ (3 : ℕ) (fun t : ℝ => p (x + t • v)) 0 := by
    intro p hp
    have hpa : ContDiffAt ℝ (3 : ℕ) p ((fun t : ℝ => x + t • v) 0) :=
      hp.contDiffAt (hΩo.mem_nhds (by simpa using hx))
    simpa [Function.comp_def] using hpa.comp (0 : ℝ) hℓ.contDiffAt
  have hφf := hrestrict f hfd
  have hφh := hrestrict h hhd
  -- The restriction of `f + h` splits, so its iterated derivatives split.
  have hsplit : (fun t : ℝ => (f + h) (x + t • v))
      = (fun t : ℝ => f (x + t • v)) + fun t : ℝ => h (x + t • v) := rfl
  have e2 : iteratedDeriv 2 (fun t : ℝ => (f + h) (x + t • v)) 0
      = iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0
        + iteratedDeriv 2 (fun t : ℝ => h (x + t • v)) 0 := by
    rw [hsplit]
    exact iteratedDeriv_add (hφf.of_le (by norm_num)) (hφh.of_le (by norm_num))
  have e3 : iteratedDeriv 3 (fun t : ℝ => (f + h) (x + t • v)) 0
      = iteratedDeriv 3 (fun t : ℝ => f (x + t • v)) 0
        + iteratedDeriv 3 (fun t : ℝ => h (x + t • v)) 0 := by
    rw [hsplit]
    exact iteratedDeriv_add hφf hφh
  -- Both second derivatives are nonnegative, so the `3/2` power is superadditive.
  have hfn := SCAddAux.line_second_deriv_nonneg hΩo hfc hfd hx v
  have hhn := SCAddAux.line_second_deriv_nonneg hΩo hhc hhd hx v
  rw [e2, e3]
  calc |iteratedDeriv 3 (fun t : ℝ => f (x + t • v)) 0
          + iteratedDeriv 3 (fun t : ℝ => h (x + t • v)) 0|
      ≤ |iteratedDeriv 3 (fun t : ℝ => f (x + t • v)) 0|
          + |iteratedDeriv 3 (fun t : ℝ => h (x + t • v)) 0| := abs_add_le _ _
    _ ≤ 2 * (iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0) ^ ((3 : ℝ) / 2)
          + 2 * (iteratedDeriv 2 (fun t : ℝ => h (x + t • v)) 0) ^ ((3 : ℝ) / 2) :=
        add_le_add (hfi x hx v) (hhi x hx v)
    _ ≤ 2 * (iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0
          + iteratedDeriv 2 (fun t : ℝ => h (x + t • v)) 0) ^ ((3 : ℝ) / 2) := by
        have := SCAddAux.rpow_three_halves_superadditive hfn hhn
        linarith
