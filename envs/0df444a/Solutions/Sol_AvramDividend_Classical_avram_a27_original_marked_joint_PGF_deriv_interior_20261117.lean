-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_marked_joint_PGF_deriv_interior_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:47:50.339068+00:00
-- url     : https://prove2.me/submissions/56ada17e-bd75-4aeb-9c86-ab43ddf3d206

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_exp_weighted_negative_jump_count_integrable_rate_bound_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun x : ℝ => ∫ ω, x ^ (K ω) * Real.exp (θ * J ω) ∂P)
      (∫ ω, ((K ω : ℝ) * z ^ (K ω - 1)) * Real.exp (θ * J ω) ∂P)
      z := by
  let F : ℝ → Ω → ℝ := fun x ω =>
    x ^ (K ω) * Real.exp (θ * J ω)
  let D : ℝ → Ω → ℝ := fun x ω =>
    ((K ω : ℝ) * x ^ (K ω - 1)) * Real.exp (θ * J ω)
  let W : Ω → ℝ := fun ω =>
    (K ω : ℝ) * Real.exp (θ * J ω)
  have hWeight :
      Integrable W P :=
    (avram_a27_original_physical_exp_weighted_negative_jump_count_integrable_rate_bound_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK hCount).1
  have hF (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      Integrable (F x) P := by
    exact avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
      X hFinite t θ hθ J hJMeas hJEq K hK x
      (le_of_lt hx.1) (le_of_lt hx.2)
  have hMeasD : Measurable (D z) := by
    have hCast : Measurable (fun ω : Ω => (K ω : ℝ)) :=
      (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hK
    have hPow : Measurable (fun ω : Ω => z ^ (K ω - 1)) :=
      (measurable_of_countable (fun n : ℕ => z ^ (n - 1))).comp hK
    have hExp : Measurable (fun ω : Ω => Real.exp (θ * J ω)) :=
      (hJMeas.const_mul θ).exp
    exact (hCast.mul hPow).mul hExp
  have hBoundPow (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
      x ^ n ≤ (1 : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      calc
        x ^ n * x ≤ x ^ n * 1 := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hx.2)
            (pow_nonneg (le_of_lt hx.1) _)
        _ = x ^ n := by ring
        _ ≤ 1 := ih
  have hDerivBound : ∀ᵐ ω ∂P, ∀ x ∈ Ioo (0 : ℝ) 1,
      ‖D x ω‖ ≤ W ω := by
    exact Filter.Eventually.of_forall (fun ω x hx => by
      have hExpNonneg : 0 ≤ Real.exp (θ * J ω) :=
        le_of_lt (Real.exp_pos _)
      have hPowerNonneg : 0 ≤ x ^ (K ω - 1) :=
        pow_nonneg (le_of_lt hx.1) _
      have hNonneg : 0 ≤ D x ω :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hPowerNonneg) hExpNonneg
      rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
      change ((K ω : ℝ) * x ^ (K ω - 1)) *
        Real.exp (θ * J ω) ≤
        (K ω : ℝ) * Real.exp (θ * J ω)
      calc
        ((K ω : ℝ) * x ^ (K ω - 1)) * Real.exp (θ * J ω) ≤
            ((K ω : ℝ) * 1) * Real.exp (θ * J ω) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hBoundPow x hx _) (Nat.cast_nonneg _))
                hExpNonneg
        _ = _ := by ring)
  have hDerivPoint : ∀ᵐ ω ∂P, ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun y => F y ω) (D x ω) x := by
    exact Filter.Eventually.of_forall (fun ω x hx => by
      exact (hasDerivAt_pow (K ω) x).mul_const (Real.exp (θ * J ω)))
  have hFEventually :
      ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (F x) P := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with x hx
    exact (hF x hx).aestronglyMeasurable
  have hh :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := D) (bound := W)
      (s := Ioo (0 : ℝ) 1) (x₀ := z)
      (Ioo_mem_nhds hz.1 hz.2)
      hFEventually (hF z hz) hMeasD.aestronglyMeasurable
      hDerivBound hWeight hDerivPoint
  exact hh.2
