-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.separated_set_packing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:16.421257+00:00
-- url     : https://prove2.me/submissions/81458ec9-4c35-47a0-97af-9f2d98bb356d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SeparatedSetPackingBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open MeasureTheory Set Metric
open scoped Function ENNReal
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : SeparatedSetPackingBound := by
  intro E _ _ _ s r δ hδ hr hs h
  borelize E
  let μ : Measure E := Measure.addHaar
  have δpos : 0 < δ / 2 := by positivity
  have ρpos : 0 < r + δ / 2 := by positivity
  set A := ⋃ c ∈ s, ball (c : E) (δ / 2) with hA
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) (δ / 2)) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have := h c hc d hd hcd
    linarith
  have A_subset : A ⊆ ball (0 : E) (r + δ / 2) := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    have := hs x hx
    linarith
  have I :
    (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ Module.finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((r + δ / 2) ^ Module.finrank ℝ E) * μ (ball 0 1) :=
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ Module.finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [hA, measure_biUnion_finset D fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ δpos]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) (r + δ / 2)) := measure_mono A_subset
      _ = ENNReal.ofReal ((r + δ / 2) ^ Module.finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ ρpos]
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ Module.finrank ℝ E) ≤
      ENNReal.ofReal ((r + δ / 2) ^ Module.finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) * (δ / 2) ^ Module.finrank ℝ E ≤ (r + δ / 2) ^ Module.finrank ℝ E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg ρpos.le _) J
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg δpos.le _)] at this
  have e : 1 + 2 * r / δ = (r + δ / 2) / (δ / 2) := by
    field_simp
    ring
  rw [e, div_pow, le_div_iff₀ (pow_pos δpos _)]
  exact K
end Formalism.HermitianLattices.TraceIntegrality
