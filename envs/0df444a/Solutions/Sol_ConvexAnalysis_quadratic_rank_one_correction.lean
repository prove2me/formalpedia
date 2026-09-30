-- Prove2me | solution 1 for ConvexAnalysis.quadratic_rank_one_correction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-30T00:11:37.112676+00:00
-- url     : https://prove2.me/submissions/3f6c510b-ed85-45a6-879d-2a573a818e0e

import Mathlib.Tactic.Abel
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.NormNum
open NormedSpace
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem solution (L : E →L[ℝ] ℝ) (q : E → ℝ)
    (hq : Continuous q) (hhom : ∀ r : ℝ, ∀ v : E, q (r • v) = r ^ 2 * q v)
    (htan : ∀ v : E, v ≠ 0 → L v = 0 → 0 < q v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : E, v ≠ 0 → 0 < q v + c * (L v) ^ 2 := by
  let T : Set E := {v | ‖v‖ = 1}
  have hT : IsCompact T := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : E) 1
  let B := T ∩ {v | q v ≤ 0}
  have hB : IsCompact B := hT.inter_right (isClosed_le hq continuous_const)
  have hL : Continuous (fun v : E => (L v) ^ 2) := L.continuous.pow 2
  have hLpos : ∀ v ∈ B, 0 < (L v) ^ 2 := by
    intro v hv
    have hvne : v ≠ 0 := by
      intro he
      have hvnorm : ‖v‖ = 1 := hv.1
      norm_num [he] at hvnorm
    have hLv : L v ≠ 0 := by
      intro he
      have hpos := htan v hvne he
      exact (not_lt_of_ge hv.2) hpos
    exact sq_pos_of_ne_zero hLv
  have hunit : ∃ c : ℝ, 0 < c ∧ ∀ v ∈ T, 0 < q v + c * (L v) ^ 2 := by
    rcases B.eq_empty_or_nonempty with hempty | hne
    · refine ⟨1, zero_lt_one, ?_⟩
      intro v hv
      have hqpos : 0 < q v := by
        by_contra hh
        have hvB : v ∈ B := ⟨hv, le_of_not_gt hh⟩
        rw [hempty] at hvB
        exact hvB
      nlinarith [sq_nonneg (L v)]
    · obtain ⟨u, hu, hminL⟩ := hB.exists_isMinOn hne hL.continuousOn
      obtain ⟨w, hw, hminq⟩ := hB.exists_isMinOn hne hq.continuousOn
      let α := (L u) ^ 2
      let M := max 0 (-q w)
      let c := (M + 1) / α
      have hα : 0 < α := hLpos u hu
      have hM : 0 ≤ M := le_max_left _ _
      have hc : 0 < c := div_pos (by linarith) hα
      have hca : c * α = M + 1 := div_mul_cancel₀ _ hα.ne'
      have hqM : -M ≤ q w := by
        have hh : -q w ≤ M := le_max_right _ _
        linarith
      refine ⟨c, hc, ?_⟩
      intro v hv
      by_cases hqpos : 0 < q v
      · exact add_pos_of_pos_of_nonneg hqpos (mul_nonneg hc.le (sq_nonneg _))
      · have hvB : v ∈ B := ⟨hv, le_of_not_gt hqpos⟩
        have hαv : α ≤ (L v) ^ 2 := hminL hvB
        have hqv : q w ≤ q v := hminq hvB
        have hmul := mul_le_mul_of_nonneg_left hαv hc.le
        nlinarith
  obtain ⟨c, hc, hcu⟩ := hunit
  refine ⟨c, hc, ?_⟩
  intro v hv
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : normalize v ∈ T := norm_normalize hv
  have hpos := hcu _ hu
  have hqv : q v = ‖v‖ ^ 2 * q (normalize v) := by
    simpa only [norm_smul_normalize] using hhom ‖v‖ (normalize v)
  have hLv : L v = ‖v‖ * L (normalize v) := by
    simpa only [norm_smul_normalize, smul_eq_mul] using L.map_smul ‖v‖ (normalize v)
  calc
    0 < ‖v‖ ^ 2 * (q (normalize v) + c * (L (normalize v)) ^ 2) :=
      mul_pos (sq_pos_of_pos hnorm) hpos
    _ = q v + c * (L v) ^ 2 := by rw [hqv, hLv]; ring
