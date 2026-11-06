-- Prove2me | solution 1 for BianchiIX.exists_normalized_connection_regular_interval
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:48:34.487339+00:00
-- url     : https://prove2.me/submissions/90e11199-b555-4251-85d8-31f33c542bce

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_exists_Ioo_covering_Icc
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_Ioo_covering_of_eventually {s t : ℝ} {P : ℝ → Prop} (hst : s ≤ t)
    (hP : ∀ u ∈ Icc s t, ∀ᶠ v in 𝓝 u, P v) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ ∀ u ∈ Ioo l r, P u := by
  obtain ⟨l, r, hls, htr, hsub⟩ := exists_Ioo_covering_Icc hst isOpen_interior
    (fun u hu => mem_interior_iff_mem_nhds.mpr (hP u hu))
  exact ⟨l, r, hls, htr, fun u hu => interior_subset (hsub hu)⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiff_connectionClockRate (n : WithTop ℕ∞) : ContDiff ℝ n connectionClockRate := by
  unfold connectionClockRate connectionSpeed coupling
  fun_prop

end
end

theorem solution {x : NormalizedState} {t₀ s t : ℝ}
    (hst : s ≤ t) (hdom : Icc s t ⊆ normalizedMaxDomain x t₀)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0)
    (hw : ∀ u ∈ Icc s t, 0 < toProjectiveState (normalizedMaxCurve x t₀ u) 3)
    (hD : ∀ u ∈ Icc s t, 0 < connectionClockRate (toProjectiveState (normalizedMaxCurve x t₀ u))) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ ∀ u ∈ Ioo l r,
      u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0 ∧
      0 < toProjectiveState (normalizedMaxCurve x t₀ u) 3 ∧
      0 < connectionClockRate (toProjectiveState (normalizedMaxCurve x t₀ u)) := by
  apply exists_Ioo_covering_of_eventually hst
  intro u hu
  have hα := (hasDerivAt_normalizedMaxCurve (hdom hu)).continuousAt
  have hAc : ContinuousAt (fun v => 1 + normalizedMaxCurve x t₀ v 0) u :=
    continuousAt_const.add ((continuous_apply 0).continuousAt.comp hα)
  have hβ : ContinuousAt (fun v => toProjectiveState (normalizedMaxCurve x t₀ v)) u :=
    (contDiffAt_toProjectiveState 1 (ne_of_gt (hA u hu))).continuousAt.comp hα
  have hwc := (continuous_apply (3 : Fin 4)).continuousAt.comp hβ
  have hDc := (contDiff_connectionClockRate 1).continuous.continuousAt.comp hβ
  have hmem : ∀ᶠ v in 𝓝 u, v ∈ normalizedMaxDomain x t₀ :=
    (isOpen_normalizedMaxDomain x t₀).mem_nhds (hdom hu)
  exact hmem.and ((hAc.eventually (isOpen_Ioi.mem_nhds (hA u hu))).and
    ((hwc.eventually (isOpen_Ioi.mem_nhds (hw u hu))).and
      (hDc.eventually (isOpen_Ioi.mem_nhds (hD u hu)))))
