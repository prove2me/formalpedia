-- Prove2me | solution 1 for BianchiIX.contDiffOn_ode_family_with_derivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:08:31.983221+00:00
-- url     : https://prove2.me/submissions/d8aa49f4-4e2d-45ac-9697-e82f72cf6395

import Theorems.Thm_BianchiIX_ode_variation_remainder
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
import Mathlib.Analysis.Calculus.FDeriv.Partial


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter Metric Asymptotics
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]


/-- A continuous variational family supplies the derivative of the solution family. -/
theorem solution {f : E → E} (hf : ContDiff ℝ 2 f)
    {x₀ : E} {t₀ r ε : ℝ} (hε : 0 < ε)
    {α : E × ℝ → E} {J : E × ℝ → E →L[ℝ] E} {L : ℝ≥0}
    (hcα : ContinuousOn α (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)))
    (hcJ : ContinuousOn J (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)))
    (hα0 : ∀ x ∈ ball x₀ r, α (x, t₀) = x)
    (hJ0 : ∀ x ∈ ball x₀ r, J (x, t₀) = ContinuousLinearMap.id ℝ E)
    (hα : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => α (x, u)) (f (α (x, t))) t)
    (hJ : ∀ x ∈ ball x₀ r, ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      HasDerivAt (fun u => J (x, u)) ((fderiv ℝ f (α (x, t))).comp (J (x, t))) t)
    (hLip : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
      LipschitzOnWith L (fun x => α (x, t)) (ball x₀ r)) :
    ContDiffOn ℝ 1 α (ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ z ∈ ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε), HasStrictFDerivAt α
        ((J z).coprod ((ContinuousLinearMap.id ℝ ℝ).smulRight (f (α z)))) z := by
  let U := ball x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)
  have ho : IsOpen U := isOpen_ball.prod isOpen_Ioo
  have hDU : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  obtain ⟨B, hB⟩ := ((isCompact_closedBall x₀ r).prod
    (isCompact_Icc (a := t₀ - ε) (b := t₀ + ε))).exists_bound_of_continuousOn hcα
  obtain ⟨C, hC⟩ := hDU.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : E) B) (isCompact_closedBall (0 : E) B)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) B).exists_bound_of_continuousOn
    hDU.continuous.continuousOn
  have hstate {x : E} (hx : x ∈ ball x₀ r) {u : ℝ} (hu : u ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      α (x, u) ∈ closedBall (0 : E) B := by
    rw [mem_closedBall, dist_zero_right]
    exact hB (x, u) ⟨ball_subset_closedBall hx, Ioo_subset_Icc_self hu⟩
  have hdx (x : E) (hx : x ∈ ball x₀ r) (t : ℝ) (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      HasFDerivAt (fun y => α (y, t)) (J (x, t)) x := by
    have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
    have hseg : uIcc t₀ t ⊆ Ioo (t₀ - ε) (t₀ + ε) :=
      (convex_Ioo _ _).ordConnected.uIcc_subset ht₀ ht
    have hO : (fun y => α (y, t) - α (x, t) - J (x, t) (y - x))
        =O[𝓝 x] (fun y => ‖y - x‖ ^ 2) := by
      apply IsBigO.of_bound (gronwallBound 0 K (C * (L : ℝ) ^ 2) |t - t₀|)
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      have H := ode_variation_remainder (fun z => (hf.differentiable (by norm_num) z).hasFDerivAt)
        (convex_closedBall (0 : E) B) hC
        (fun u hu => hα x hx u (hseg hu)) (fun u hu => hα y hy u (hseg hu))
        (fun _ hu => hstate hx (hseg hu)) (fun _ hu => hstate hy (hseg hu))
        (fun u hu => hJ x hx u (hseg hu)) (hJ0 x hx)
        (fun u hu => hK _ (hstate hx (hseg hu)))
        (fun u hu => by
          rw [hα0 y hy, hα0 x hx]
          exact (hLip u (hseg hu)).norm_sub_le hy hx)
      simpa only [hα0 y hy, hα0 x hx, norm_pow, norm_norm] using H
    exact hasFDerivAt_iff_isLittleO.mpr (hO.trans_isLittleO (isLittleO_pow_sub_sub x (by norm_num)))
  let V : E × ℝ → ℝ →L[ℝ] E := fun z =>
    (ContinuousLinearMap.id ℝ ℝ).smulRight (f (α z))
  have hcαU : ContinuousOn α U := hcα.mono (fun _ hz => ⟨ball_subset_closedBall hz.1, Ioo_subset_Icc_self hz.2⟩)
  have hcV : ContinuousOn V U :=
    (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)).continuous.comp_continuousOn
      (hf.continuous.comp_continuousOn hcαU)
  have hd (z : E × ℝ) (hz : z ∈ U) : HasStrictFDerivAt α ((J z).coprod (V z)) z := by
    apply hasStrictFDerivAt_uncurry_coprod (f := fun x t => α (x, t))
      (f₁ := fun x t => J (x, t)) (f₂ := fun x t => V (x, t))
    · filter_upwards [ho.mem_nhds hz] with w hw
      exact hdx w.1 hw.1 w.2 hw.2
    · filter_upwards [ho.mem_nhds hz] with w hw
      exact (hα w.1 hw.1 w.2 hw.2).hasFDerivAt
    · exact hcJ.continuousAt (ho.mem_nhds hz)
    · exact hcV.continuousAt (ho.mem_nhds hz)
  refine ⟨?_, hd⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn ho.uniqueDiffOn]
  exact ⟨by simp, fun z => (J z).coprod (V z),
    contDiffOn_zero.mpr (hcJ.continuousLinearMapCoprod hcV),
    fun z hz => (hd z hz).hasFDerivAt.hasFDerivWithinAt⟩
