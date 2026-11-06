-- Prove2me | solution 1 for BianchiIX.exists_connectionReturn_log_clock
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T09:46:46.054196+00:00
-- url     : https://prove2.me/submissions/0d9afa95-830f-4b98-a8d3-e4e06fe09457

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ConnectionClock
import Definitions.Def_BianchiIX_Dynamics_ConnectionClockDifferential
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_exists_connection_first_return
import Theorems.Thm_BianchiIX_exists_normalized_connectionLog_reparametrization
import Theorems.Thm_BianchiIX_exists_normalized_connection_regular_interval
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Theorems.Thm_BianchiIX_projective_inverse_scale
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

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

private theorem BianchiIX.connection_denom_bound {m u v w : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w ∧ 0 < projectiveDenom (-m) u v w := by
  have H : 3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w := by
    dsimp [projectiveDenom, curvature]
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu.1,
      mul_le_mul_of_nonneg_left hw.2 hu.1, sq_nonneg u, sq_nonneg (v - w)]
  exact ⟨H, by nlinarith only [H, hu.2, sq_nonneg m]⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveOriginalFlow_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveOriginalFlow y t₀ t₀ = y := by
  rw [projectiveOriginalFlow, normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt hD)

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

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connection_entry_denom_pos {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    0 < projectiveStateDenom (connectionEntry (p 0) (p 1) (p 2)) := by
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ 1 / 10000 :=
    ⟨hu.1, hu.2.trans (div_le_self (by norm_num) (by linarith only [hμ]))⟩
  exact (connection_denom_bound (m := p 0) (v := 1) hu' (by norm_num)
    ⟨hw.1.le, hw.2.trans (by norm_num)⟩).2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.connectionReturn_growing_component {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    connectionReturnState p 3 = 1 ∧ ∀ v : ConnectionParameters, fderiv ℝ connectionReturnState p v 3 = 0 := by
  have H := connectionReturn_regular hμ hu hw
  have heq : (fun q => connectionReturnState q 3) =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
    filter_upwards [H.2.2.2.2.2] with q hq
    exact hq.1.1.2.2
  have hd := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) p).congr_of_eventuallyEq heq
  have hc := (hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) (connectionReturnState p)).comp p
    ((H.2.2.1.differentiableAt (by norm_num)).hasFDerivAt)
  refine ⟨heq.self_of_nhds, ?_⟩
  intro v
  have hlinear := hc.unique hd
  exact congrArg (fun L : ConnectionParameters →L[ℝ] ℝ => L v) hlinear

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.connectionReturn_control {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    0 < connectionReturnTime p ∧ ∀ t ∈ Icc 0 (connectionReturnTime p),
      3 / (2 * (p 0) ^ 2) ≤ 1 + normalizedMaxCurve (connectionInitialState p) 0 t 0 ∧
        connectionRegion (p 0) (toProjectiveState (normalizedMaxCurve (connectionInitialState p) 0 t)) := by
  obtain ⟨T, hT, hfirst, hprefix, _⟩ := exists_connection_first_return hμ hu hw
  have heq : connectionReturnTime p = T := hfirst.csInf_eq
  rw [heq]
  exact ⟨hT, hprefix⟩

end
end

/-- The full canonical first return supplies every geometric and clock hypothesis of the variation estimates. -/
theorem solution {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    let y := connectionEntry (p 0) (p 1) (p 2)
    let L := -Real.log (p 2)
    0 ≤ L ∧ ∃ q : ℝ → ℝ, q 0 = 0 ∧ q L = connectionReturnTime p ∧
      ∀ z ∈ Icc 0 L,
        q z ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 (q z) 0 ∧
        connectionRegion (p 0) (projectiveOriginalFlow y 0 (q z)) ∧
        0 < projectiveOriginalFlow y 0 (q z) 1 ∧
        0 < projectiveOriginalFlow y 0 (q z) 2 ∧
        0 < projectiveOriginalFlow y 0 (q z) 3 ∧
        HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y 0 (q z))) z := by
  intro y L
  let T := connectionReturnTime p
  let β : ℝ → ProjectiveState := projectiveOriginalFlow y 0
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0 := ⟨hu.1.le, hu.2⟩
  have hden := connection_entry_denom_pos hμ hu' hw
  have hc : stateConstraint (fromProjectiveState y) = 1 := fromProjectiveState_constraint (ne_of_gt hden)
  have hvalid := (connectionReturn_regular hμ hu' hw).1
  have hcontrol := connectionReturn_control hμ hu' hw
  have hT : 0 < T := hcontrol.1
  have hdom (t : ℝ) (ht : t ∈ Icc 0 T) : t ∈ normalizedMaxDomain (fromProjectiveState y) 0 := (hvalid.2.1 t ht).1
  have hA (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 := (hvalid.2.1 t ht).2
  have hregion (t : ℝ) (ht : t ∈ Icc 0 T) : connectionRegion (p 0) (β t) := (hcontrol.2 t ht).2
  have hinit : β 0 = y := projectiveOriginalFlow_initial hden 0
  have hentry (i : Fin 3) : 0 < β 0 i.succ := by
    rw [hinit]
    fin_cases i
    · exact hu.1
    · change (0 : ℝ) < 1
      norm_num
    · exact hw.1
  have hpos (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin 3) : 0 < β t i.succ :=
    normalized_projective_wall_pos (hdom 0 ⟨le_rfl, hT.le⟩) (hdom t ht)
      (hA 0 ⟨le_rfl, hT.le⟩) (hA t ht) i (hentry i)
  have hD (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < connectionClockRate (β t) := by
    have H := (connection_speed_bounds hμ (hregion t ht).1 (hregion t ht).2.1
      (hregion t ht).2.2.1 (hregion t ht).2.2.2).1
    change p 0 / 2 ≤ connectionClockRate (β t) at H
    linarith only [H, hμ]
  obtain ⟨l, r, hl, hr, hregular⟩ := exists_normalized_connection_regular_interval hT.le hdom hA
    (fun t ht => hpos t ht 2) hD
  have hcover : Icc 0 T ⊆ Ioo l r := fun t ht => ⟨hl.trans_le ht.1, ht.2.trans_lt hr⟩
  have h0I := hcover ⟨le_rfl, hT.le⟩
  have hTI := hcover ⟨hT.le, le_rfl⟩
  obtain ⟨e, hsrc, heq, htarget, hzero, hinv0, hmono, hflow⟩ :=
    exists_normalized_connectionLog_reparametrization (convex_Ioo l r) isOpen_Ioo h0I
      (fun t ht => (hregular t ht).1) hc (fun t ht => (hregular t ht).2.1)
      (fun t ht => (hregular t ht).2.2.1) (fun t ht => (hregular t ht).2.2.2)
  have he0 : e 0 = 0 := by rw [heq 0 h0I]; exact sub_self _
  have hWend : β T 3 = 1 := (connectionReturn_growing_component hμ hu' hw).1
  have heT : e T = L := by
    rw [heq T hTI]
    change Real.log (β T 3) - Real.log (β 0 3) = L
    rw [hWend, hinit]
    simp [L, y, connectionEntry]
  have hTE : T ∈ e.source := by rwa [hsrc]
  have hL : 0 ≤ L := by simpa only [he0, heT] using hmono.monotoneOn h0I hTI hT.le
  have hzt (z : ℝ) (hz : z ∈ Icc 0 L) : z ∈ e.target :=
    htarget.ordConnected.out hzero (heT ▸ e.map_source hTE) hz
  have hinv (z : ℝ) (hz : z ∈ Icc 0 L) : e.symm z ∈ Icc 0 T := by
    have hxI : e.symm z ∈ Ioo l r := by rw [← hsrc]; exact e.map_target (hzt z hz)
    constructor
    · apply (hmono.le_iff_le h0I hxI).mp
      rw [he0, e.right_inv (hzt z hz)]
      exact hz.1
    · apply (hmono.le_iff_le hxI hTI).mp
      rw [e.right_inv (hzt z hz), heT]
      exact hz.2
  refine ⟨hL, e.symm, hinv0, ?_, ?_⟩
  · rw [← heT]
    exact e.left_inv hTE
  · intro z hz
    have ht := hinv z hz
    refine ⟨hdom _ ht, hA _ ht, hregion _ ht, hpos _ ht 0, hpos _ ht 1, hpos _ ht 2, ?_⟩
    have hc' := (normalizedMaxCurve_constraint (hdom _ ht)).trans hc
    have hscale := projective_inverse_scale (ne_of_gt (hA _ ht)) hc'
    change 6 / projectiveStateDenom (β (e.symm z)) = 1 + normalizedMaxCurve (fromProjectiveState y) 0 (e.symm z) 0 at hscale
    change HasDerivAt e.symm (1 / connectionOriginalClockRate (β (e.symm z))) z
    rw [connectionOriginalClockRate, hscale]
    exact (hflow z (hzt z hz)).1
