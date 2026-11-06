-- Prove2me | solution 1 for BianchiIX.normalized_connection_phase_band_improves
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:08:00.74788+00:00
-- url     : https://prove2.me/submissions/542165f5-3eca-4634-ae6c-9261a235fc0b

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Theorems.Thm_BianchiIX_connectionLog_phase_band_improves
import Theorems.Thm_BianchiIX_exists_normalized_connectionLog_reparametrization
import Theorems.Thm_BianchiIX_exists_normalized_connection_regular_interval
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
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

private theorem BianchiIX.connection_coupling_bounds {u v w : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -u ^ 2 ≤ coupling u v w ∧ coupling u v w ≤ 2 * u := by
  unfold coupling
  constructor
  · nlinarith only [mul_nonneg hu hv.1, mul_nonneg hu hw.1]
  · nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu,
      mul_le_mul_of_nonneg_left hw.2 hu, sq_nonneg u]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.connection_speed_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    μ / 2 ≤ connectionSpeed m u v w ∧ connectionSpeed m u v w ≤ μ := by
  obtain ⟨hc₀, hc₁⟩ := connection_coupling_bounds hu.1 hv hw
  obtain ⟨hm₀, hm₁⟩ := abs_le.mp hm
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionSpeed
  constructor <;> nlinarith only [hc₀, hc₁, hm₀, hm₁, hu.2, hu2, hμ]

end
end

/-- The strict connection-band improvement applies to actual Einstein-flow prefixes. -/
theorem solution {x : NormalizedState} {t₀ s t μ : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    -β s 0 = μ →
    (∀ u ∈ Icc s t, |-β u 0 - μ| ≤ 1 / 2) →
    (∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ 1 / 10000) →
    (∀ u ∈ Icc s t, 0 < β u 2 ∧ β u 2 ≤ 1) →
    (∀ u ∈ Icc s t, 0 < β u 3 ∧ β u 3 ≤ 1) → β s 1 ≤ β s 2 →
    |-β t 0 - μ| ≤ (3 / 2 + 12 * β s 1) / μ ∧ |-β t 0 - μ| < 1 / 2 := by
  intro β hinit hm hu hv hw hentry
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have htm : t ∈ Icc s t := ⟨hst, le_rfl⟩
  have hdom : Icc s t ⊆ normalizedMaxDomain x t₀ := fun u hh =>
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hh.1)
  have hD (u : ℝ) (hh : u ∈ Icc s t) : 0 < connectionClockRate (β u) := by
    have H := (connection_speed_bounds hμ (hm u hh) (hu u hh)
      ⟨(hv u hh).1.le, (hv u hh).2⟩ ⟨(hw u hh).1.le, (hw u hh).2⟩).1
    change μ / 2 ≤ connectionClockRate (β u) at H
    linarith only [H, hμ]
  obtain ⟨l, r, hls, htr, hregular⟩ := exists_normalized_connection_regular_interval hst hdom hA
    (fun u hh => (hw u hh).1) hD
  have hcover : Icc s t ⊆ Ioo l r := fun u hh => ⟨hls.trans_le hh.1, hh.2.trans_lt htr⟩
  have hsI := hcover hsm
  have htI := hcover htm
  obtain ⟨e, hsrc, heq, htarget, hzero, hinv0, hmono, hflow⟩ :=
    exists_normalized_connectionLog_reparametrization (convex_Ioo l r) isOpen_Ioo hsI
      (fun u hh => (hregular u hh).1) hc
      (fun u hh => (hregular u hh).2.1) (fun u hh => (hregular u hh).2.2.1)
      (fun u hh => (hregular u hh).2.2.2)
  have htE : t ∈ e.source := by rwa [hsrc]
  have hes : e s = 0 := by rw [heq s hsI]; exact sub_self _
  have hbt : 0 ≤ e t := by simpa only [hes] using hmono.monotoneOn hsI htI hst
  have hzt (z : ℝ) (hz : z ∈ Icc 0 (e t)) : z ∈ e.target :=
    htarget.ordConnected.out hzero (e.map_source htE) hz
  have hinv (z : ℝ) (hz : z ∈ Icc 0 (e t)) : e.symm z ∈ Icc s t := by
    have hzT := hzt z hz
    have hxI : e.symm z ∈ Ioo l r := by rw [← hsrc]; exact e.map_target hzT
    constructor
    · apply (hmono.le_iff_le hsI hxI).mp
      rw [hes, e.right_inv hzT]
      exact hz.1
    · apply (hmono.le_iff_le hxI htI).mp
      rw [e.right_inv hzT]
      exact hz.2
  let Y := fun z => β (e.symm z)
  have hY (z : ℝ) (hz : z ∈ Icc 0 (e t)) : HasDerivAt Y (connectionLogField (Y z)) z :=
    (hflow z (hzt z hz)).2.2
  have H := connectionLog_phase_band_improves hbt hμ hY
    (by change -β (e.symm 0) 0 = μ; rwa [hinv0])
    (fun z hz => hm _ (hinv z hz)) (fun z hz => hu _ (hinv z hz))
    (fun z hz => hv _ (hinv z hz))
    (fun z hz => ⟨(hw _ (hinv z hz)).1.le, (hw _ (hinv z hz)).2⟩)
    (by change β (e.symm 0) 1 ≤ β (e.symm 0) 2; rwa [hinv0])
  simpa only [Y, hinv0, e.left_inv htE] using H
