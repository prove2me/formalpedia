-- Prove2me | solution 1 for BianchiIX.exists_normalized_partialCore_downcrossing_two
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:32:56.671996+00:00
-- url     : https://prove2.me/submissions/c44d1840-3e52-44f2-b4c0-726e15573ef3

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_exists_activeWall_first_downcrossing_two
import Theorems.Thm_BianchiIX_exists_normalized_partialCore_return
import Theorems.Thm_BianchiIX_hasDerivAt_toProjectiveState_normalized
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_core_residence
import Theorems.Thm_BianchiIX_normalized_core_return_downward
import Theorems.Thm_BianchiIX_normalized_core_return_isLeast
import Theorems.Thm_BianchiIX_normalized_partialCore_energy_band_improves
import Theorems.Thm_BianchiIX_scaled_core_entry_upward
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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

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
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_radius_bounds {k : ℝ} {y : ProjectiveState} (hk : 6 ≤ k) (hy : coreRegion k y) :
    99 / 100 * k ≤ coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) ≤ 101 / 100 * k :=
  coreBootstrap_radius_closed hk (Real.sqrt_nonneg _)
    (by rw [coreRadius_sq]; exact hy.1)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_wall_bounds {k : ℝ} {y : ProjectiveState} (hy : coreRegion k y) :
    (0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k) ∧ (0 ≤ y 3 ∧ y 3 ≤ (1 / 10000) / k) := by
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hw0 : 0 ≤ y 3 := (mul_nonneg_iff_of_pos_left hv0).mp hy.2.2.2.1
  exact ⟨hy.2.2.1, hw0, (le_mul_of_one_le_left hw0 hy.2.1).trans hy.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_normalized_partialCore_firstReturn {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    coreRadius (β s 0) (β s 2) = k → (1 < β s 2 ∨ (β s 2 = 1 ∧ 1 ≤ β s 0)) →
    (0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k) →
    (0 ≤ β s 2 * β s 3 ∧ β s 2 * β s 3 ≤ (1 / 10000) / k) →
    ∃ t > s, IsLeast {u | s < u ∧ β u 2 = 1} t ∧
      β t 0 < 1 ∧ 0 < coreAngle (β t 0) (β t 2) ∧
      deriv (fun u => β u 2) t ≤ -(1 + normalizedMaxCurve x t₀ t 0) * k / 2 ∧
      t - s ≤ 2 * k * Real.log (4 * k) ∧ ∀ u ∈ Icc s t,
        3 / (2 * k ^ 2) ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u) ∧
        |coreRadius (β u 0) (β u 2) - k| ≤ 16 * (β s 1 + (β s 2 * β s 3) ^ 2 / k) ∧
        |coreRadius (β u 0) (β u 2) ^ 2 - k ^ 2| < 1 / 16 := by
  intro β hR hVcase hU hP
  obtain ⟨t, hst, hvt, H⟩ := exists_normalized_partialCore_return hc hk hs hA hR hVcase hU hP
  have hk0 : 0 < k := by linarith only [hk]
  have hpos (u : ℝ) (hu : u ∈ Icc s t) : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) (H u hu).1
  have hr (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_radius_bounds hk (H u hu).2
  have hv (u : ℝ) (hu : u ∈ Icc s t) : 1 ≤ β u 2 := (H u hu).2.2.1
  have hwall (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_wall_bounds (H u hu).2
  have hleast := normalized_core_return_isLeast hc hk hs hst hpos
    (fun u hu => (hr u hu).1) hv (fun u hu => (hwall u hu).1) (fun u hu => (hwall u hu).2) hvt
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have hdown := normalized_core_return_downward hc hk hs hst (hpos t htm) hvt
    (fun u hu => hv u ⟨hu.1.le, hu.2.le⟩) (hr t htm).1 (hwall t htm).1 (hwall t htm).2
  have htime := (normalized_core_residence hc hk hs hst.le hpos hr hv
    (fun u hu => (hwall u hu).1) (fun u hu => (hwall u hu).2)).2
  refine ⟨t, hst, hleast, hdown.1, hdown.2.1, hdown.2.2.1, htime, ?_⟩
  intro u hu
  have hsub : Icc s u ⊆ Icc s t := fun v hv => ⟨hv.1, hv.2.trans hu.2⟩
  have Henergy := normalized_partialCore_energy_band_improves hc hk hs hu.1
    (fun v hv => hpos v (hsub hv)) hR
    (fun v hv => by rw [coreRadius_sq]; exact (H v (hsub hv)).2.1)
    (fun v hv' => hv v (hsub hv')) (fun v hv => (H v (hsub hv)).2.2.2.1)
    (fun v hv => (H v (hsub hv)).2.2.2.2)
  exact ⟨(H u hu).1, (H u hu).2, Henergy⟩

end
end


/-- The outgoing event remains the first negative crossing on an ambient neighborhood of an incoming-boundary entry. -/
theorem solution {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    coreRadius (β s 0) (β s 2) = k → (1 < β s 2 ∨ (β s 2 = 1 ∧ 1 ≤ β s 0)) →
    (0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k) →
    (0 ≤ β s 2 * β s 3 ∧ β s 2 * β s 3 ≤ (1 / 10000) / k) →
    ∃ t > s, IsLeast {u | s < u ∧ β u 2 = 1} t ∧
      (∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u)) ∧
      ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 2 τ x ∧
        ContDiffAt ℝ 2 (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y))) x ∧
        HasFDerivAt τ (normalizedEventTimeDifferential projectiveActiveWall x t₀ t) x ∧
        HasFDerivAt (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y)))
          ((fderiv ℝ toProjectiveState (normalizedMaxCurve x t₀ t)).comp
            (normalizedEventDifferential projectiveActiveWall x t₀ t)) x ∧
        (∀ᶠ y in 𝓝 x,
          IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain y t₀ ∧
            projectiveActiveWall (normalizedMaxCurve y t₀ u) = 1 ∧
            normalizedEventRate projectiveActiveWall y t₀ u < 0} (τ y) ∧
          (∀ u ∈ Icc s (τ y), u ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ u 0)) := by
  intro β hR hV hU hP
  obtain ⟨t, hst, hfirst, _, _, hder, _, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk hs hA hR hV hU hP
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6) hk
  have hcore (u : ℝ) (hu : u ∈ Icc s t) :
      0 < 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u) :=
    ⟨lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) (H u hu).1, (H u hu).2.1⟩
  have hreg (u : ℝ) (hu : u ∈ Icc s t) :
      u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
    ⟨normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1), (hcore u hu).1⟩
  have HD (u : ℝ) (hu : u ∈ Icc s t) : HasDerivAt (fun v => β v 2)
      (normalizedEventRate projectiveActiveWall x t₀ u) u :=
    ((contDiffAt_projectiveActiveWall 1 (ne_of_gt (hreg u hu).2)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt u (hasDerivAt_normalizedMaxCurve (hreg u hu).1)
  have hbefore (u : ℝ) (hu : u ∈ Ico s t) :
      projectiveActiveWall (normalizedMaxCurve x t₀ u) ≠ 1 ∨
        0 < normalizedEventRate projectiveActiveWall x t₀ u := by
    rcases eq_or_lt_of_le hu.1 with heq | hsu
    · subst u
      rcases hV with hv | ⟨hv, hm⟩
      · exact Or.inl (ne_of_gt hv)
      · right
        have hsm : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
        have Hflow := normalizedMaxCurve_forward_of_constraint hc hs
        have Hup := scaled_core_entry_upward hk hA
          (hasDerivAt_toProjectiveState_normalized Hflow.1 hA.ne' Hflow.2.1) hv hm
          (coreRegion_radius_bounds hk (hcore s hsm).2).1 hU
          (coreRegion_wall_bounds (hcore s hsm).2).2
        rw [(HD s hsm).deriv] at Hup
        exact (by positivity : 0 < (1 + normalizedMaxCurve x t₀ s 0) * k / 2).trans_le Hup.2.1
    · left
      intro hh
      exact (not_le_of_gt hu.2) (hfirst.2 ⟨hsu, hh⟩)
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  rw [(HD t htm).deriv] at hder
  have hrate : normalizedEventRate projectiveActiveWall x t₀ t < 0 := hder.trans_lt (by
    have Hpos := (hcore t htm).1
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos Hpos) hkpos) (by norm_num))
  exact ⟨t, hst, hfirst, hcore,
    exists_activeWall_first_downcrossing_two hst hreg hbefore hrate hfirst.1.2⟩
