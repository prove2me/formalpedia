-- Prove2me | solution 1 for DiazModulus.nongeneric_rational_modulus_orbit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-29T06:40:58.179671+00:00
-- url     : https://prove2.me/submissions/dac2aefe-5119-4d7b-a68b-7d8feb582b0c

import Mathlib
import Theorems.Thm_DiazModulus_log_pair_rigid_of_trdeg_one
import Theorems.Thm_Transcendence_trdeg_adjoin_le_one_of_isAlgebraic_adjoin

/-!
# Rational squared moduli over `ℚ[π]`

Let `u, v` be non-zero logarithms of algebraic numbers with `u * conj u = ru` and
`v * conj v = rv` rational, both algebraic over `A = ℚ[π]`.

* Since `v ≠ 0`, the rational `rv` is non-zero, and `c = ru / rv` satisfies
  `u * conj u = c * (v * conj v)`.
* From `w * conj w = r` with `w ≠ 0` we get `conj w = r * w⁻¹`, which is algebraic over `A`
  whenever `w` is. So `u, v, conj u, conj v` are all algebraic over `A = ℚ[π]`, and the
  subalgebra they generate over `ℚ` has transcendence degree at most one.
* Rigidity of logarithm pairs of transcendence degree at most one then gives `q ∈ ℚ` with
  `v = q * u` or `v = q * conj u`.
-/

open ComplexConjugate

namespace R1_nongeneric_rational_modulus_orbit

/-- A rational number is algebraic over any `ℚ`-subalgebra of `ℂ`. -/
theorem isAlgebraic_ratCast_subalgebra (A : Subalgebra ℚ ℂ) (r : ℚ) :
    IsAlgebraic A (r : ℂ) := by
  have h := isAlgebraic_algebraMap (R := A) (A := ℂ) (algebraMap ℚ A r)
  have e : algebraMap A ℂ (algebraMap ℚ A r) = (r : ℂ) := by
    rw [← IsScalarTower.algebraMap_apply ℚ A ℂ r, eq_ratCast (algebraMap ℚ ℂ) r]
  rwa [e] at h

/-- If `w ≠ 0` has rational squared modulus `w * conj w = r` and is algebraic over a
`ℚ`-subalgebra `A` of `ℂ`, then `conj w = r * w⁻¹` is algebraic over `A` as well. -/
theorem isAlgebraic_conj (A : Subalgebra ℚ ℂ) (w : ℂ) (hw : w ≠ 0) (r : ℚ)
    (hr : w * conj w = r) (hwa : IsAlgebraic A w) : IsAlgebraic A (conj w) := by
  have e : conj w = (r : ℂ) * w⁻¹ := by
    rw [← hr, mul_comm w (conj w), mul_assoc, mul_inv_cancel₀ hw, mul_one]
  rw [e]
  exact (isAlgebraic_ratCast_subalgebra A r).mul hwa.inv

/-- The squared modulus of a non-zero complex number is non-zero. -/
theorem ratCast_ne_zero_of_mul_conj (w : ℂ) (hw : w ≠ 0) (r : ℚ) (hr : w * conj w = r) :
    r ≠ 0 := by
  intro h0
  rw [h0, Rat.cast_zero, Complex.mul_conj, Complex.ofReal_eq_zero] at hr
  exact (Complex.normSq_pos.mpr hw).ne' hr

end R1_nongeneric_rational_modulus_orbit

open R1_nongeneric_rational_modulus_orbit in
theorem solution (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (heu : IsAlgebraic ℚ (Complex.exp u)) (hev : IsAlgebraic ℚ (Complex.exp v))
    (ru rv : ℚ) (hru : u * conj u = ru) (hrv : v * conj v = rv)
    (hua : IsAlgebraic (Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)) u)
    (hva : IsAlgebraic (Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)) v) :
    ∃ q : ℚ, v = (q : ℂ) * u ∨ v = (q : ℂ) * conj u := by
  have hrv0 : rv ≠ 0 := ratCast_ne_zero_of_mul_conj v hv rv hrv
  have hc : u * conj u = ((ru / rv : ℚ) : ℂ) * (v * conj v) := by
    rw [hru, hrv, Rat.cast_div, div_mul_cancel₀ (ru : ℂ) (Rat.cast_ne_zero.mpr hrv0)]
  have hS : ∀ s ∈ ({u, v, conj u, conj v} : Set ℂ),
      IsAlgebraic (Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)) s := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact hua
    · exact hva
    · exact isAlgebraic_conj _ u hu ru hru hua
    · exact isAlgebraic_conj _ v hv rv hrv hva
  have htr := Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin (K := ℚ)
    ((Real.pi : ℝ) : ℂ) ({u, v, conj u, conj v} : Set ℂ) hS
  exact DiazModulus.log_pair_rigid_of_trdeg_one u v hu hv heu hev (ru / rv) hc htr
