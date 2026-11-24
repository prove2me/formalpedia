-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.tailRay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:46.055996+00:00
-- url     : https://prove2.me/submissions/6d6bd64d-7a85-44b8-b477-8f42e764a8c6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset MeasureTheory
open scoped ComplexOrder
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution : Formalism.HermitianLattices.CumulantEstimateDefs.TailAlongRay := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.TailAlongRay
  intro n t₀ α Q₀ hn ht hnα hQα
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast at hnα
  have ha : -t₀⁻¹ < 0 := neg_lt_zero.2 (inv_pos.2 ht)
  have hK0 : 0 ≤ t₀ ^ m * Real.exp (1 - α) := by positivity
  have hgI : IntegrableOn (fun t => t₀ ^ m * Real.exp (1 - α) * Real.exp (-t₀⁻¹ * t)) (Set.Ioi t₀) :=
    (integrableOn_exp_mul_Ioi ha t₀).const_mul _
  have hbound : ∀ t ∈ Set.Ioi t₀, t ^ m * Real.exp (-(α * (t / t₀))) ≤
      t₀ ^ m * Real.exp (1 - α) * Real.exp (-t₀⁻¹ * t) := by
    intro t ht'
    have htt : t₀ < t := ht'
    obtain ⟨s, hs⟩ : ∃ s, s = t / t₀ := ⟨_, rfl⟩
    have hs1 : 1 ≤ s := by rw [hs]; exact (one_le_div ht).2 htt.le
    have hts : t = t₀ * s := by rw [hs]; field_simp
    have e1 : -t₀⁻¹ * t = -s := by rw [hts]; field_simp
    rw [← hs, e1, hts, mul_pow]
    have hpow : s ^ m ≤ Real.exp ((m : ℝ) * (s - 1)) := by
      rw [Real.exp_nat_mul]
      have hse : s ≤ Real.exp (s - 1) := by linarith [Real.add_one_le_exp (s - 1)]
      first
        | exact pow_le_pow_left₀ (by linarith) hse m
        | exact pow_le_pow_left (by linarith) hse m
    have hexpo : (m : ℝ) * (s - 1) + -(α * s) ≤ (1 - α) + -s := by
      nlinarith [mul_le_mul_of_nonneg_right hnα (sub_nonneg.2 hs1)]
    calc t₀ ^ m * s ^ m * Real.exp (-(α * s))
        ≤ t₀ ^ m * Real.exp ((m : ℝ) * (s - 1)) * Real.exp (-(α * s)) := by gcongr
      _ = t₀ ^ m * Real.exp ((m : ℝ) * (s - 1) + -(α * s)) := by rw [Real.exp_add]; ring
      _ ≤ t₀ ^ m * Real.exp ((1 - α) + -s) := by gcongr
      _ = t₀ ^ m * Real.exp (1 - α) * Real.exp (-s) := by rw [Real.exp_add]; ring
  have hfI : IntegrableOn (fun t => t ^ m * Real.exp (-(α * (t / t₀)))) (Set.Ioi t₀) := by
    refine Integrable.mono' hgI (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht' => ?_)
    have htp : 0 < t := lt_trans ht ht'
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound t ht'
  refine ⟨hfI, ?_⟩
  have hx : Real.exp (1 - α) * Real.exp (-1) = Real.exp (-α) := by
    rw [← Real.exp_add]
    ring_nf
  have hc : -t₀⁻¹ * t₀ = -1 := by field_simp
  calc ∫ t in Set.Ioi t₀, t ^ m * Real.exp (-(α * (t / t₀)))
      ≤ ∫ t in Set.Ioi t₀, t₀ ^ m * Real.exp (1 - α) * Real.exp (-t₀⁻¹ * t) :=
        setIntegral_mono_on hfI hgI measurableSet_Ioi hbound
    _ = t₀ ^ m * Real.exp (1 - α) * (-Real.exp (-t₀⁻¹ * t₀) / -t₀⁻¹) := by
        first
          | rw [integral_const_mul, integral_exp_mul_Ioi ha]
          | rw [integral_mul_const, integral_exp_mul_Ioi ha]
    _ = t₀ ^ m * t₀ * (Real.exp (1 - α) * Real.exp (-1)) := by
        rw [hc, neg_div_neg_eq, div_inv_eq_mul]
        ring
    _ = t₀ ^ (m + 1) * Real.exp (-α) := by rw [hx, pow_succ]
    _ ≤ t₀ ^ (m + 1) * Real.exp (-(Q₀ / 2)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
