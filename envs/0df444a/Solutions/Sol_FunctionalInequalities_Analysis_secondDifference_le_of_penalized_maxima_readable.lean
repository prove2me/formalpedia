-- Prove2me | solution 1 for FunctionalInequalities.Analysis.secondDifference_le_of_penalized_maxima_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:14.471919+00:00
-- url     : https://prove2.me/submissions/d093467f-a920-44bd-a714-94b4f1d830ef

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondDifference
import Theorems.Thm_FunctionalInequalities_Analysis_sd_penalized_estimate_readable

noncomputable section
open scoped RealInnerProductSpace
section LT17CPenalizedMaximumBound
open Set
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E]
/-- **Second-difference bound from penalised maxima** (weak Letwin route; KLS500
`weak_moment_symmetricSecondDifference_le_of_uniformlyConvex_target`, algebraic part): let `u` be convex and
differentiable, bounded below, and `V` differentiable with `V − (κ/2)‖·‖²` convex. Suppose that for every
`η > 0` the penalised second difference `Δ²ₕu − η u` has a maximiser `x₀` at which the log-density
`F := V ∘ ∇u − u` satisfies the comparison `F(x₀ + h) + F(x₀ − h) − 2 F(x₀) ≤ η n`. Then
`u(x + h) + u(x − h) − 2 u(x) ≤ 4 ‖h‖² / κ` everywhere. -/
theorem solution {u V : E → ℝ} (hconv : ConvexOn ℝ univ u)
    (hu : Differentiable ℝ u) (hV : Differentiable ℝ V) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ univ (fun y => V y - (κ / 2) * ‖y‖ ^ 2)) {C : ℝ}
    (hC : ∀ x, |fderiv ℝ V (gradient u x) (gradient u x)| ≤ C) {m : ℝ} (hm : ∀ x, m ≤ u x)
    (n : ℕ) (h : E)
    (hmax : ∀ η > 0, ∃ x₀ : E,
      (∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
        u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀) ∧
      (V (gradient u (x₀ + h)) - u (x₀ + h)) + (V (gradient u (x₀ - h)) - u (x₀ - h)) -
        2 * (V (gradient u x₀) - u x₀) ≤ η * n) :
    ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ 4 * ‖h‖ ^ 2 / κ := by
  intro x
  have hb : ∀ η > 0, u (x + h) + u (x - h) - 2 * u x ≤
      4 * ‖h‖ ^ 2 / κ + 2 * ‖h‖ * Real.sqrt (η * ((n : ℝ) + C) / κ) +
        η * (u x - m) := by
    intro η hη
    obtain ⟨x₀, hmaximum, hcomparison⟩ := hmax η hη
    have hD := FunctionalInequalities.Analysis.sd_penalized_estimate_readable hconv hu hV hκ hstrong hC
      n h x₀ hη hmaximum hcomparison
    have hx := hmaximum x
    have hlower := mul_le_mul_of_nonneg_left (hm x₀) hη.le
    linarith only [hD, hx, hlower]
  have hc : Continuous (fun η : ℝ =>
      4 * ‖h‖ ^ 2 / κ + 2 * ‖h‖ * Real.sqrt (η * ((n : ℝ) + C) / κ) +
        η * (u x - m)) :=
    (continuous_const.add
      (continuous_const.mul
        (Real.continuous_sqrt.comp
          ((continuous_id.mul continuous_const).div_const κ)))).add
      (continuous_id.mul continuous_const)
  have hl : Filter.Tendsto
      (fun η : ℝ =>
        4 * ‖h‖ ^ 2 / κ + 2 * ‖h‖ * Real.sqrt (η * ((n : ℝ) + C) / κ) +
          η * (u x - m))
      (nhdsWithin 0 (Ioi 0)) (nhds (4 * ‖h‖ ^ 2 / κ)) := by
    simpa only [zero_mul, zero_div, Real.sqrt_zero, mul_zero, add_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
  apply ge_of_tendsto hl
  exact Filter.Eventually.mono self_mem_nhdsWithin (fun η hη => hb η hη)
