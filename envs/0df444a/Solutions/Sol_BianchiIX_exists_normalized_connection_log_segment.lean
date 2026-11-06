-- Prove2me | solution 1 for BianchiIX.exists_normalized_connection_log_segment
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:29:30.112789+00:00
-- url     : https://prove2.me/submissions/16a637f9-c11c-4c15-bfbc-71da53f9e63f

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Theorems.Thm_BianchiIX_exists_normalized_connectionLog_reparametrization
import Theorems.Thm_BianchiIX_exists_normalized_connection_regular_interval
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Real.Lemmas
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
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set

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

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.toProjectiveState_wall_sign {x : NormalizedState} (hA : 0 < 1 + x 0) (i : Fin 3) :
    (toProjectiveState x i.succ = 0 ↔ wallValue i x = 0) ∧
      (0 ≤ toProjectiveState x i.succ ↔ 0 ≤ wallValue i x) := by
  have heq : toProjectiveState x i.succ = Real.sqrt 3 * wallValue i x / (1 + x 0) := by
    fin_cases i <;> rfl
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [heq]
  constructor
  · simp only [div_eq_zero_iff, mul_eq_zero, ne_of_gt hsqrt, ne_of_gt hA, false_or, or_false]
  · rw [div_eq_mul_inv, mul_nonneg_iff_of_pos_right (inv_pos.mpr hA), mul_nonneg_iff_of_pos_left hsqrt]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_projective_wall_sign {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (β t i.succ = 0 ↔ β s i.succ = 0) ∧ (0 ≤ β t i.succ ↔ 0 ≤ β s i.succ) := by
  have H := normalized_wall_sign (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
    (fun _ hh => hasDerivAt_normalizedMaxCurve hh) hs ht i
  exact ⟨(toProjectiveState_wall_sign hAt i).1.trans (H.1.trans (toProjectiveState_wall_sign hAs i).1.symm),
    (toProjectiveState_wall_sign hAt i).2.trans (H.2.trans (toProjectiveState_wall_sign hAs i).2.symm)⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_projective_wall_pos {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) (hi : 0 < toProjectiveState (normalizedMaxCurve x t₀ s) i.succ) :
    0 < toProjectiveState (normalizedMaxCurve x t₀ t) i.succ := by
  have H := normalized_projective_wall_sign hs ht hAs hAt i
  have hne : toProjectiveState (normalizedMaxCurve x t₀ t) i.succ ≠ 0 :=
    fun h => (ne_of_gt hi) (H.1.mp h)
  exact lt_of_le_of_ne (H.2.mpr hi.le) hne.symm

end
end


/-- The whole actual closed prefix is represented by one inverse logarithmic clock. -/
theorem solution {x : NormalizedState} {t₀ s t μ : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    let L := Real.log (β t 3) - Real.log (β s 3)
    (∀ u ∈ Icc s t, connectionRegion μ (β u)) → 0 < β s 3 →
    0 ≤ L ∧ ∃ q : ℝ → ℝ, q 0 = s ∧ q L = t ∧ MapsTo q (Icc 0 L) (Icc s t) ∧
      (∀ u ∈ Icc s t, ∃ z ∈ Icc 0 L, q z = u) ∧
      (∀ z ∈ Icc 0 L, HasDerivAt (fun v => β (q v)) (connectionLogField (β (q z))) z) := by
  intro β L hregion hw
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have htm : t ∈ Icc s t := ⟨hst, le_rfl⟩
  have hdom : Icc s t ⊆ normalizedMaxDomain x t₀ := fun u hu =>
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
  have hwpos (u : ℝ) (hu : u ∈ Icc s t) : 0 < β u 3 :=
    normalized_projective_wall_pos (hdom hsm) (hdom hu) (hA s hsm) (hA u hu) 2 hw
  have hD (u : ℝ) (hu : u ∈ Icc s t) : 0 < connectionClockRate (β u) := by
    have H := (connection_speed_bounds hμ (hregion u hu).1 (hregion u hu).2.1
      (hregion u hu).2.2.1 (hregion u hu).2.2.2).1
    change μ / 2 ≤ connectionClockRate (β u) at H
    linarith only [H, hμ]
  obtain ⟨l, r, hls, htr, hregular⟩ := exists_normalized_connection_regular_interval hst hdom hA hwpos hD
  have hcover : Icc s t ⊆ Ioo l r := fun u hu => ⟨hls.trans_le hu.1, hu.2.trans_lt htr⟩
  have hsI := hcover hsm
  have htI := hcover htm
  obtain ⟨e, hsrc, heq, htarget, hzero, hinv0, hmono, hflow⟩ :=
    exists_normalized_connectionLog_reparametrization (convex_Ioo l r) isOpen_Ioo hsI
      (fun u hu => (hregular u hu).1) hc (fun u hu => (hregular u hu).2.1)
      (fun u hu => (hregular u hu).2.2.1) (fun u hu => (hregular u hu).2.2.2)
  have hes : e s = 0 := by rw [heq s hsI]; exact sub_self _
  have het : e t = L := heq t htI
  have htE : t ∈ e.source := by rwa [hsrc]
  have hL : 0 ≤ L := by simpa only [hes, het] using hmono.monotoneOn hsI htI hst
  have hzt (z : ℝ) (hz : z ∈ Icc 0 L) : z ∈ e.target :=
    htarget.ordConnected.out hzero (het ▸ e.map_source htE) hz
  have hinv (z : ℝ) (hz : z ∈ Icc 0 L) : e.symm z ∈ Icc s t := by
    have hzT := hzt z hz
    have hxI : e.symm z ∈ Ioo l r := by rw [← hsrc]; exact e.map_target hzT
    constructor
    · apply (hmono.le_iff_le hsI hxI).mp
      rw [hes, e.right_inv hzT]
      exact hz.1
    · apply (hmono.le_iff_le hxI htI).mp
      rw [e.right_inv hzT, het]
      exact hz.2
  refine ⟨hL, e.symm, hinv0, ?_, hinv, ?_, fun z hz => (hflow z (hzt z hz)).2.2⟩
  · rw [← het]
    exact e.left_inv htE
  · intro u hu
    have huI := hcover hu
    refine ⟨e u, ⟨?_, ?_⟩, e.left_inv (by rwa [hsrc])⟩
    · simpa only [hes] using hmono.monotoneOn hsI huI hu.1
    · simpa only [het] using hmono.monotoneOn huI htI hu.2
