-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures.cauchy_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:34:06.559631+00:00
-- url     : https://prove2.me/submissions/744232ca-0c5c-4d20-bf49-13bab4f84e2e

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_IntegralExpInt
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ExponentialIntegralMeasures_integral_exp_int
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ExponentialIntegralMeasures_muT_real_univ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures
namespace Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures
theorem _root_.solution (G : ℕ) (Θ : (Fin G → ℂ) → ℂ) (c : (Fin G → ℕ) → ℂ)
    (hΘ : ∀ z : Fin G → ℂ, HasSum (fun e : Fin G → ℕ => c e * ∏ i, z i ^ e i) (Θ z))
    (r : Fin G → ℝ) (B : ℝ)
    (hB : ∀ θ : Fin G → ℝ, ‖Θ (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))‖ ≤ B)
    (e : Fin G → ℕ) : ‖c e‖ * ∏ i, |r i| ^ e i ≤ B := by
  set zθ : (Fin G → ℝ) → Fin G → ℂ := fun θ i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I) with hzθ
  set w : (Fin G → ℝ) → ℂ := fun θ => ∏ i, Complex.exp (-(e i : ℂ) * I * (θ i : ℂ)) with hw
  set F : (Fin G → ℕ) → (Fin G → ℝ) → ℂ :=
    fun e' θ => c e' * (∏ i, zθ θ i ^ e' i) * w θ with hF
  set a : (Fin G → ℕ) → ℂ := fun e' => c e' * ∏ i, ((r i : ℂ)) ^ e' i with ha
  set k : (Fin G → ℕ) → Fin G → ℤ := fun e' i => (e' i : ℤ) - (e i : ℤ) with hk
  have key : ∀ e' θ, F e' θ = a e' * ∏ i, Complex.exp (((k e' i : ℤ) : ℂ) * I * (θ i : ℂ)) := by
    intro e' θ
    simp only [hF, ha, hw, hzθ, hk]
    rw [mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_pow, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have hnormexp : ∀ (m : ℤ) (t : ℝ), ‖Complex.exp ((m : ℂ) * I * (t : ℂ))‖ = 1 := by
    intro m t
    rw [Complex.norm_exp]; simp
  have hnormF : ∀ e' θ, ‖F e' θ‖ = ‖a e'‖ := by
    intro e' θ
    rw [key, norm_mul, norm_prod]
    simp [hnormexp]
  have hcont : ∀ e', Continuous (F e') := by
    intro e'
    have : F e' = fun θ => a e' * ∏ i, Complex.exp (((k e' i : ℤ) : ℂ) * I * (θ i : ℂ)) :=
      funext (key e')
    rw [this]
    fun_prop
  have hint : ∀ e', Integrable (F e') (muT G) := by
    intro e'
    exact Integrable.of_bound (hcont e').aestronglyMeasurable ‖a e'‖
      (Filter.Eventually.of_forall fun θ => (hnormF e' θ).le)
  have hsumr : Summable a := (hΘ (fun i => (r i : ℂ))).summable
  have hsum : Summable fun e' => ∫ θ, ‖F e' θ‖ ∂(muT G) := by
    simp_rw [hnormF, integral_const, smul_eq_mul]
    exact (summable_norm_iff.mpr hsumr).mul_left _
  have htsum : ∀ θ, ∑' e', F e' θ = Θ (zθ θ) * w θ := fun θ => ((hΘ (zθ θ)).mul_right (w θ)).tsum_eq
  have hI : ∀ e', ∫ θ, F e' θ ∂(muT G) =
      a e' * ∏ i, (if k e' i = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) := by
    intro e'
    simp_rw [key]
    rw [integral_const_mul]
    congr 1
    rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin G => mu1)
      (fun i (t : ℝ) => Complex.exp (((k e' i : ℤ) : ℂ) * I * (t : ℂ)))]
    apply Finset.prod_congr rfl
    intro i _
    exact integral_exp_int (k e' i)
  have hmain : ∫ θ, Θ (zθ θ) * w θ ∂(muT G) = a e * ((2 * Real.pi : ℝ) : ℂ) ^ G := by
    simp_rw [← htsum]
    rw [← integral_tsum_of_summable_integral_norm hint hsum]
    rw [tsum_eq_single e]
    · rw [hI]; congr 1
      simp [hk]
    · intro e' he'
      rw [hI]
      obtain ⟨i, hi⟩ : ∃ i, e' i ≠ e i := by
        by_contra h; push Not at h; exact he' (funext h)
      have : k e' i ≠ 0 := by simp only [hk]; omega
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg this), mul_zero]
  have hbound : ‖∫ θ, Θ (zθ θ) * w θ ∂(muT G)‖ ≤ B * (muT G).real Set.univ := by
    apply norm_integral_le_of_norm_le_const
    refine Filter.Eventually.of_forall fun θ => ?_
    rw [norm_mul, hw, norm_prod]
    have : ∀ i ∈ Finset.univ, ‖Complex.exp (-(e i : ℂ) * I * (θ i : ℂ))‖ = 1 := by
      intro i _; rw [Complex.norm_exp]; simp
    rw [Finset.prod_congr rfl this, Finset.prod_const_one, mul_one]
    exact hB θ
  rw [hmain, muT_real_univ, norm_mul, norm_pow] at hbound
  have h2pi : (0:ℝ) < (2 * Real.pi) ^ G := by positivity
  have hn2 : ‖((2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn2] at hbound
  have ha' : ‖a e‖ = ‖c e‖ * ∏ i, |r i| ^ e i := by
    simp only [ha, norm_mul, norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [← ha']
  exact le_of_mul_le_mul_right hbound h2pi
end Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures
