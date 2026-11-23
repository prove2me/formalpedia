-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.fock_monomial_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:29.711787+00:00
-- url     : https://prove2.me/submissions/e9b3f48d-f831-4eba-adb7-abfe92771d5d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BlockOperatorNormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.TraceIntegrality
open MeasureTheory Finset
private lemma fock_real_integral (Om : ℝ) (hOm : 0 < Om) (k : ℕ) :
    ∫ z : ℂ, ‖z‖ ^ k * Real.exp (-‖z‖ ^ 2 / Om) =
      Real.pi * Om ^ ((k : ℝ) / 2 + 1) * Real.Gamma ((k : ℝ) / 2 + 1) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := k) (b := Om⁻¹)
    (by norm_num) (by linarith) (inv_pos.mpr hOm)
  have e : ∀ z : ℂ, ‖z‖ ^ (k : ℝ) * Real.exp (-Om⁻¹ * ‖z‖ ^ (2 : ℝ)) =
      ‖z‖ ^ k * Real.exp (-‖z‖ ^ 2 / Om) := by
    intro z
    rw [Real.rpow_natCast, Real.rpow_two]
    congr 2
    field_simp
  simp_rw [e] at h
  rw [h, Real.inv_rpow hOm.le, ← Real.rpow_neg hOm.le]
  have h1 : -(-((k : ℝ) + 2) / 2) = (k : ℝ) / 2 + 1 := by ring
  have h2 : ((k : ℝ) + 2) / 2 = (k : ℝ) / 2 + 1 := by ring
  rw [h1, h2]
  ring
private lemma fock_real_integrable (Om : ℝ) (hOm : 0 < Om) (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ k * Real.exp (-‖z‖ ^ 2 / Om)) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  by_contra hn
  have h0 := integral_undef hn
  rw [fock_real_integral Om hOm k] at h0
  have : 0 < Real.pi * Om ^ ((k : ℝ) / 2 + 1) * Real.Gamma ((k : ℝ) / 2 + 1) := by
    have := Real.Gamma_pos_of_pos (s := (k : ℝ) / 2 + 1) (by positivity)
    have := Real.rpow_pos_of_pos hOm ((k : ℝ) / 2 + 1)
    have := Real.pi_pos
    positivity
  linarith
private lemma fock_integrable (Om : ℝ) (hOm : 0 < Om) (p q : ℕ) :
    Integrable
      (fun z : ℂ => z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ)) := by
  refine (fock_real_integrable Om hOm (p + q)).mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · refine Filter.Eventually.of_forall (fun z => ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_pow, RCLike.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), pow_add]
private lemma fock_rotate (Om : ℝ) (p q : ℕ) (c : Circle) :
    ∫ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) =
      ((c : ℂ) ^ p * (starRingEnd ℂ (c : ℂ)) ^ q) *
        ∫ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) := by
  have hmp : MeasurePreserving (rotation c) (volume : Measure ℂ) volume :=
    (rotation c).measurePreserving
  have h := hmp.integral_comp (rotation c).toHomeomorph.measurableEmbedding
    (fun z : ℂ => z ^ p * (starRingEnd ℂ z) ^ q * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ))
  conv_lhs => rw [← h]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only [rotation_apply, map_mul, norm_mul, Circle.norm_coe, one_mul, mul_pow]
  ring
end Formalism.HermitianLattices.TraceIntegrality
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open MeasureTheory Finset
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : FockMonomialOrthogonality := by
  intro Om p q hOm
  refine ⟨fock_integrable Om hOm p q, ?_⟩
  split_ifs with hpq
  · subst hpq
    have e : ∀ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ p * (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) =
        ((‖z‖ ^ (2 * p) * Real.exp (-‖z‖ ^ 2 / Om) : ℝ) : ℂ) := by
      intro z
      rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rw [pow_mul]
    simp_rw [e]
    rw [integral_complex_ofReal, fock_real_integral Om hOm (2 * p)]
    congr 1
    have h1 : ((2 * p : ℕ) : ℝ) / 2 + 1 = (p : ℝ) + 1 := by push_cast; ring
    rw [h1, Real.Gamma_nat_eq_factorial, Real.rpow_add hOm, Real.rpow_natCast, Real.rpow_one]
    ring
  ·
    have hd : ((p : ℝ) - q) ≠ 0 := by
      intro h
      apply hpq
      have : (p : ℝ) = q := by linarith
      exact_mod_cast this
    set θ : ℝ := Real.pi / ((p : ℝ) - q) with hθ
    have hrot := fock_rotate Om p q (Circle.exp θ)
    have hc : ((Circle.exp θ : Circle) : ℂ) ^ p * (starRingEnd ℂ ((Circle.exp θ : Circle) : ℂ)) ^ q
        = -1 := by
      rw [Circle.coe_exp, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
        ← Complex.exp_add]
      have : (p : ℂ) * ((θ : ℂ) * Complex.I) + (q : ℂ) * (starRingEnd ℂ) ((θ : ℂ) * Complex.I)
          = (Real.pi : ℂ) * Complex.I := by
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
        have hd' : ((p : ℂ) - q) ≠ 0 := by exact_mod_cast hd
        rw [hθ]
        push_cast
        field_simp
        ring
      rw [this, Complex.exp_pi_mul_I]
    rw [hc] at hrot
    have h2 : (2 : ℂ) * ∫ z : ℂ, z ^ p * (starRingEnd ℂ z) ^ q *
        (Real.exp (-‖z‖ ^ 2 / Om) : ℂ) = 0 := by
      linear_combination hrot
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
end Formalism.HermitianLattices.TraceIntegrality
