-- Prove2me | solution 1 for BianchiIX.normalized_exit_first_hit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T17:57:39.129225+00:00
-- url     : https://prove2.me/submissions/3f163647-ec98-4781-a192-059aca7a95eb

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_projectiveActiveWall_fderiv_field
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_of_coreRadius {m v : ℝ} (hm : m < 1) :
    exitTailGap (coreRadius m v) v = 1 - m := by
  unfold exitTailGap
  rw [coreRadius_sq]
  dsimp only [coreEnergy]
  rw [add_sub_cancel_right, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hm] : m - 1 < 0)]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_compact {R v : ℝ} (hR : 7 / 4 ≤ R) (hv : 0 ≤ v ∧ v ≤ 1) :
    1 ≤ exitTailGap R v ∧ exitTailGap R v ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  refine ⟨?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by nlinarith only [hR, hv2])).mpr
      (by nlinarith only [hR, hv2])
  · exact (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTail_coupling_bound {u v w : ℝ} (hv : 0 ≤ v) :
    |coupling u v w| ≤ |u| * v + (|u| + |w|) ^ 2 := by
  have H : |v + w - u| ≤ v + |w| + |u| := by
    exact (abs_sub _ _).trans (add_le_add ((abs_add_le v w).trans_eq (by rw [abs_of_nonneg hv])) le_rfl)
  rw [coupling, abs_mul]
  have H' := mul_le_mul_of_nonneg_left H (abs_nonneg u)
  nlinarith only [H', mul_nonneg (abs_nonneg u) (abs_nonneg w), sq_nonneg |w|]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailSpeed_compact {R u v w : ℝ} (hR : 7 / 4 ≤ R)
    (hu : |u| ≤ 1 / 100) (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    1 / 2 ≤ exitTailSpeed R u v w := by
  have ht := (exitTailGap_compact hR hv).1
  have hc := exitTail_coupling_bound (u := u) (w := w) hv.1
  have huv : |u| * v ≤ 1 / 100 := by
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 (abs_nonneg u), hu]
  have hb : (|u| + |w|) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := by
    nlinarith only [hu, hw, abs_nonneg u, abs_nonneg w]
  have H := neg_abs_le (coupling u v w)
  dsimp only [exitTailSpeed]
  linarith only [ht, hc, huv, hb, H]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitClockRate_tail {y : ProjectiveState} (hm : y 0 < 1) :
    exitClockRate y = exitTailSpeed (coreRadius (y 0) (y 2)) (y 1) (y 2) (y 3) := by
  dsimp only [exitClockRate, exitTailSpeed]
  rw [exitTailGap_of_coreRadius hm]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitClockRate_compact {y : ProjectiveState} (hm : y 0 < 1)
    (hR : 7 / 4 ≤ coreRadius (y 0) (y 2))
    (hu : |y 1| ≤ 1 / 100) (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : |y 3| ≤ 1 / 100) :
    1 / 2 ≤ exitClockRate y := by
  rw [exitClockRate_tail hm]
  exact exitTailSpeed_compact hR hu hv hw

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitPhysicalRegion_clock {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : 1 / 2 ≤ exitClockRate y :=
  exitClockRate_compact (lt_of_le_of_lt hy.1 (by norm_num)) hy.2.1.1 hy.2.2.1
    ⟨(hh.trans_le hy.2.2.2.1.1).le, hy.2.2.2.1.2⟩ hy.2.2.2.2

end
end

private theorem BianchiIX.normalized_exit_active_rate_neg {x : NormalizedState} {t₀ t h : ℝ}
    (hc : stateConstraint x = 1) (hh : 0 < h) (ht : t₀ ≤ t)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (hy : exitPhysicalRegion h (toProjectiveState (normalizedMaxCurve x t₀ t))) :
    normalizedEventRate projectiveActiveWall x t₀ t < 0 := by
  have hc' := (normalizedMaxCurve_forward_of_constraint hc ht).2.1
  change fderiv ℝ projectiveActiveWall (normalizedMaxCurve x t₀ t)
    (normalizedField (normalizedMaxCurve x t₀ t)) < 0
  rw [projectiveActiveWall_fderiv_field (ne_of_gt hA) hc']
  let y := toProjectiveState (normalizedMaxCurve x t₀ t)
  have heq : activeVelocity (y 0) (y 1) (y 2) (y 3) = -exitClockRate y * y 2 := by
    dsimp only [activeVelocity, exitClockRate]
    ring
  have hD : 0 < exitClockRate y := by
    have H := exitPhysicalRegion_clock hh hy
    change 1 / 2 ≤ exitClockRate y at H
    linarith only [H]
  change (1 + normalizedMaxCurve x t₀ t 0) * activeVelocity (y 0) (y 1) (y 2) (y 3) < 0
  rw [heq]
  exact mul_neg_of_pos_of_neg hA (mul_neg_of_neg_of_pos (neg_neg_of_pos hD)
    (hh.trans_le hy.2.2.2.1.1))


/-- A completed tail crosses its lower height exactly once and has no earlier hit. -/
theorem solution {x : NormalizedState} {t₀ s t h : ℝ}
    (hc : stateConstraint x = 1) (hh : 0 < h) (hs : t₀ ≤ s) (hst : s < t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, exitPhysicalRegion h (β u)) → β t 2 = h →
    IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain x t₀ ∧ β u 2 = h} t ∧
      StrictAntiOn (fun u => β u 2) (Icc s t) ∧ (∀ u ∈ Ico s t, h < β u 2) ∧
      (∀ u ∈ Icc s t, normalizedEventRate projectiveActiveWall x t₀ u < 0) := by
  intro β hreg hhit
  have hdom (u : ℝ) (hu : u ∈ Icc s t) :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
  have hrate (u : ℝ) (hu : u ∈ Icc s t) :=
    normalized_exit_active_rate_neg hc hh (hs.trans hu.1) (hA u hu) (hreg u hu)
  have hderiv (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivAt (fun v => β v 2) (normalizedEventRate projectiveActiveWall x t₀ u) u := by
    exact ((contDiffAt_projectiveActiveWall 1 (ne_of_gt (hA u hu))).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt u (hasDerivAt_normalizedMaxCurve (hdom u hu))
  have hanti : StrictAntiOn (fun u => β u 2) (Icc s t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (HasDerivAt.continuousOn hderiv)
    intro u hu
    rw [(hderiv u (interior_subset hu)).deriv]
    exact hrate u (interior_subset hu)
  have htmem : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  refine ⟨⟨⟨hst, hdom t htmem, hhit⟩, ?_⟩, hanti, ?_, hrate⟩
  · intro u hu
    by_contra hn
    have hut : u < t := lt_of_not_ge hn
    have H := hanti ⟨hu.1.le, hut.le⟩ htmem hut
    change β t 2 < β u 2 at H
    rw [hhit, hu.2.2] at H
    exact lt_irrefl _ H
  · intro u hu
    have H := hanti ⟨hu.1, hu.2.le⟩ htmem hu.2
    change β t 2 < β u 2 at H
    rwa [hhit] at H
