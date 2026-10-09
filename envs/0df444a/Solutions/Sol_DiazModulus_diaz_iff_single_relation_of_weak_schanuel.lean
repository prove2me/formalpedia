-- Prove2me | solution 1 for DiazModulus.diaz_iff_single_relation_of_weak_schanuel
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T09:02:16.743402+00:00
-- url     : https://prove2.me/submissions/d3660277-50fb-4019-8f12-0af885b0a2e6

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_candidate_im_mem_pi_rat_of_weak_schanuel
import Theorems.Thm_DiazModulus_leaf_iff_one

open Complex ComplexConjugate

/-!
# Under weak Schanuel (n = 2), Diaz's conjecture is equivalent to a single relation

Claim: assuming the `n = 2` case of the weak Schanuel conjecture, Diaz's modulus conjecture holds
iff `t² + π²` is transcendental for every non-zero real `t` with `e^t` algebraic.

`leaf_iff_one` already says that this single relation is equivalent to Diaz's implication for
the `u` with real `exp u`, `exp u ≠ 1` and `u` off both axes. The forward direction is therefore
unconditional: Diaz's conjecture gives that left side at once. For the converse, let `u` be a
candidate. `candidate_im_mem_pi_rat_of_weak_schanuel` gives `Re u ≠ 0` and `Im u = qπ` with
`q ∈ ℚ` non-zero. Put `N = den q` and `v = N u`. Then `Im v = (num q) π`, which is a non-zero
multiple of `π`, so `exp v` is real; `Re v = N Re u ≠ 0`, so `exp v ≠ 1`; `|v| = N |u|` is
algebraic. So `v` meets all the hypotheses of the left side of `leaf_iff_one`, which says
`exp v` is transcendental. That contradicts `exp v = (exp u)^N`, which is algebraic.
-/

namespace R7_wscIff

open DiazModulus

/-- At a candidate `u` with `Re u ≠ 0` and `Im u = qπ`, the multiple `den q • u` satisfies all
the hypotheses of the left side of `leaf_iff_one`, and `exp` of it is algebraic. -/
theorem exists_multiple {u : ℂ} (hun : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ))
    (hue : IsAlgebraic ℚ (Complex.exp u)) (hre : u.re ≠ 0) {q : ℚ} (hq : q ≠ 0)
    (him : u.im = (q : ℝ) * Real.pi) :
    ∃ v : ℂ, v ≠ 0 ∧ IsAlgebraic ℚ ((‖v‖ : ℝ) : ℂ) ∧ (Complex.exp v).im = 0 ∧
      v.im ≠ 0 ∧ Complex.exp v ≠ 1 ∧ v.re ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp v) := by
  set N : ℕ := q.den with hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hNq : (N : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    have h := Rat.mul_den_eq_num q
    have h' : ((q * q.den : ℚ) : ℝ) = ((q.num : ℚ) : ℝ) := by rw [h]
    push_cast at h'
    rw [mul_comm]; exact h'
  have hvre : ((N : ℂ) * u).re = N * u.re := by simp
  have hvim : ((N : ℂ) * u).im = (q.num : ℝ) * Real.pi := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    rw [him, ← mul_assoc, hNq]
  have hvre0 : ((N : ℂ) * u).re ≠ 0 := by rw [hvre]; exact mul_ne_zero hN0 hre
  refine ⟨(N : ℂ) * u, ?_, ?_, ?_, ?_, ?_, hvre0, ?_⟩
  · intro h0; apply hvre0; rw [h0]; simp
  · have h : ((‖(N : ℂ) * u‖ : ℝ) : ℂ) = (N : ℂ) * ((‖u‖ : ℝ) : ℂ) := by
      rw [norm_mul, Complex.norm_natCast]; push_cast; ring
    rw [h]
    exact (isAlgebraic_natCast N).mul hun
  · rw [Complex.exp_im, hvim, Real.sin_int_mul_pi, mul_zero]
  · rw [hvim]
    exact mul_ne_zero (by exact_mod_cast Rat.num_ne_zero.2 hq) Real.pi_ne_zero
  · intro h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
    apply hvre0
    rw [hn]; simp
  · rw [Complex.exp_nat_mul]
    exact hue.pow N

end R7_wscIff

open DiazModulus R7_wscIff in
theorem solution
    (hWSC : ∀ a b : ℂ,
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({a, b, Complex.exp a, Complex.exp b} : Set ℂ)) < 2 →
      ∃ m n k : ℤ, (m ≠ 0 ∨ n ≠ 0) ∧
        (m : ℂ) * a + (n : ℂ) * b = 2 * ((Real.pi : ℝ) : ℂ) * Complex.I * (k : ℂ)) :
    DiazModulusConjecture ↔
      ∀ t : ℝ, t ≠ 0 → IsAlgebraic ℚ ((Real.exp t : ℝ) : ℂ) →
        Transcendental ℚ ((t ^ 2 + Real.pi ^ 2 : ℝ) : ℂ) := by
  rw [← DiazModulus.leaf_iff_one]
  constructor
  · intro hD u hu hmod _ _ _ _
    exact hD u hu hmod
  · intro hL u hu hmod hue
    obtain ⟨hre, q, hq, him⟩ :=
      DiazModulus.candidate_im_mem_pi_rat_of_weak_schanuel hWSC ⟨hu, hmod, hue⟩
    obtain ⟨v, hv0, hvn, hvi, hvim, hv1, hvre, hve⟩ :=
      exists_multiple hmod hue hre hq him
    exact hL v hv0 hvn hvi hvim hv1 hvre hve
