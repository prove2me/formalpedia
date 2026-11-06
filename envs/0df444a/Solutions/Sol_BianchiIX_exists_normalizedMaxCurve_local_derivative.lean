-- Prove2me | solution 1 for BianchiIX.exists_normalizedMaxCurve_local_derivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:22:08.559652+00:00
-- url     : https://prove2.me/submissions/abd5a456-3598-4582-9629-bcf0116a5c2b

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Theorems.Thm_BianchiIX_contDiff_normalizedField
import Theorems.Thm_BianchiIX_exists_normalizedMaxCurve_local_dependence
import Theorems.Thm_BianchiIX_exists_normalized_variation_family
import Theorems.Thm_BianchiIX_normalized_variation_remainder
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter Metric Asymptotics
open scoped Topology NNReal

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.contDiff_normalizedDifferential (n : WithTop ℕ∞) :
    ContDiff ℝ n normalizedDifferential :=
  (contDiff_normalizedField (n + 1)).fderiv_right le_rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.normalizedDifferential_lipschitz_closedBall (x : NormalizedState) (r : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K normalizedDifferential (closedBall x r) :=
  (contDiff_normalizedDifferential 1).contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall x r) (isCompact_closedBall x r)

end
end

/-- The constructed variational family is the actual initial-state derivative of the exact flow. -/
theorem solution (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ J : NormalizedState × ℝ → NormalizedVariation,
      ContinuousOn (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
        (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ContinuousOn J (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ x ∈ ball x₀ r,
        Ioo (t₀ - ε) (t₀ + ε) ⊆ normalizedMaxDomain x t₀ ∧
        J (x, t₀) = ContinuousLinearMap.id ℝ NormalizedState ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (J (x, t)) x ∧
          HasDerivAt (fun u => J (x, u))
            ((normalizedDifferential (normalizedMaxCurve x t₀ t)).comp (J (x, t))) t := by
  obtain ⟨r₀, hr₀, ε₀, hε₀, L, hdom, hc, hLip⟩ :=
    exists_normalizedMaxCurve_local_dependence x₀ t₀
  obtain ⟨r₁, hr₁, ε₁, hε₁, J, hcJ, hJ⟩ := exists_normalized_variation_family x₀ t₀
  have hclosed : Icc (t₀ - ε₀ / 2) (t₀ + ε₀ / 2) ⊆ Ioo (t₀ - ε₀) (t₀ + ε₀) := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ r₀).prod
    (isCompact_Icc (a := t₀ - ε₀ / 2) (b := t₀ + ε₀ / 2))).exists_bound_of_continuousOn
      (hc.mono (prod_subset_prod_right hclosed))
  obtain ⟨C, hC⟩ := normalizedDifferential_lipschitz_closedBall 0 B
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : NormalizedState) B).exists_bound_of_continuousOn
    (contDiff_normalizedDifferential 1).continuous.continuousOn
  let r := min r₀ r₁
  let ε := min (ε₀ / 2) ε₁
  have hr : 0 < r := lt_min hr₀ hr₁
  have hε : 0 < ε := lt_min (by linarith) hε₁
  have hx₀ {x : NormalizedState} (hx : x ∈ ball x₀ r) : x ∈ closedBall x₀ r₀ :=
    closedBall_subset_closedBall (min_le_left _ _) (ball_subset_closedBall hx)
  have hx₁ {x : NormalizedState} (hx : x ∈ ball x₀ r) : x ∈ closedBall x₀ r₁ :=
    closedBall_subset_closedBall (min_le_right _ _) (ball_subset_closedBall hx)
  have htclosed {u : ℝ} (hu : u ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      u ∈ Icc (t₀ - ε₀ / 2) (t₀ + ε₀ / 2) := by
    have H : ε ≤ ε₀ / 2 := min_le_left _ _
    constructor <;> linarith [hu.1, hu.2]
  have ht₁ {u : ℝ} (hu : u ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      u ∈ Ioo (t₀ - ε₁) (t₀ + ε₁) := by
    have H : ε ≤ ε₁ := min_le_right _ _
    constructor <;> linarith [hu.1, hu.2]
  have hstate {x : NormalizedState} (hx : x ∈ ball x₀ r)
      {u : ℝ} (hu : u ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      normalizedMaxCurve x t₀ u ∈ closedBall (0 : NormalizedState) B := by
    rw [mem_closedBall, dist_zero_right]
    exact hB (x, u) ⟨hx₀ hx, htclosed hu⟩
  refine ⟨r, hr, ε, hε, J,
    hc.mono (fun z hz => ⟨hx₀ hz.1, hclosed (htclosed hz.2)⟩),
    hcJ.mono (fun z hz => ⟨hx₁ hz.1, ht₁ hz.2⟩), fun x hx => ?_⟩
  refine ⟨fun u hu => hdom x (hx₀ hx) (hclosed (htclosed hu)), (hJ x (hx₁ hx)).2.1,
    fun t ht => ⟨?_, (hJ x (hx₁ hx)).2.2 t (ht₁ ht)⟩⟩
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  have hseg : uIcc t₀ t ⊆ Ioo (t₀ - ε) (t₀ + ε) :=
    (convex_Ioo _ _).ordConnected.uIcc_subset ht₀ ht
  have hO : (fun y => normalizedMaxCurve y t₀ t - normalizedMaxCurve x t₀ t - J (x, t) (y - x))
      =O[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
    apply IsBigO.of_bound (gronwallBound 0 K (C * (L : ℝ) ^ 2) |t - t₀|)
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    have H := normalized_variation_remainder (convex_closedBall (0 : NormalizedState) B)
      hC
      (fun u hu => hasDerivAt_normalizedMaxCurve (hdom x (hx₀ hx) (hclosed (htclosed (hseg hu)))))
      (fun u hu => hasDerivAt_normalizedMaxCurve (hdom y (hx₀ hy) (hclosed (htclosed (hseg hu)))))
      (fun _ hu => hstate hx (hseg hu)) (fun _ hu => hstate hy (hseg hu))
      (fun u hu => (hJ x (hx₁ hx)).2.2 u (ht₁ (hseg hu))) (hJ x (hx₁ hx)).2.1
      (fun u hu => hK _ (hstate hx (hseg hu)))
      (fun u hu => by
        simpa only [normalizedMaxCurve_initial] using
          (hLip u (hclosed (htclosed (hseg hu)))).norm_sub_le (hx₀ hy) (hx₀ hx))
    simpa only [normalizedMaxCurve_initial, norm_pow, norm_norm] using H
  exact hasFDerivAt_iff_isLittleO.mpr (hO.trans_isLittleO (isLittleO_pow_sub_sub x (by norm_num)))
