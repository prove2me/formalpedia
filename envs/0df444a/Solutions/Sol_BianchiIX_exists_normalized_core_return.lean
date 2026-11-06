-- Prove2me | solution 1 for BianchiIX.exists_normalized_core_return
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:45:03.775169+00:00
-- url     : https://prove2.me/submissions/fbfa7fb5-eb7f-4864-8bb2-e46aa4538818

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_isClosed_normalized_core_times
import Theorems.Thm_BianchiIX_normalized_core_energy_band_improves
import Theorems.Thm_BianchiIX_normalized_core_local_prefix
import Theorems.Thm_BianchiIX_normalized_core_residence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

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

/-- Every admissible large-parameter entrance completes a core return in the exact Einstein flow. -/
theorem solution {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    coreRadius (β s 0) (β s 2) = k → β s 2 = 1 → 1 ≤ β s 0 →
    (0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k) →
    (0 ≤ β s 3 ∧ β s 3 ≤ (1 / 10000) / k) →
    ∃ t > s, β t 2 = 1 ∧ ∀ u ∈ Icc s t,
      3 / (2 * k ^ 2) ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u) := by
  intro β hR hV hM hU hW
  have hk0 : 0 < k := by linarith
  let c := 3 / (2 * k ^ 2)
  have hc0 : 0 < c := by dsimp [c]; positivity
  let S : Set ℝ := {u | c ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u)}
  let T := s + 2 * k * Real.log (4 * k) + 1
  have hlog : 0 < Real.log (4 * k) := Real.log_pos (by linarith)
  have hsT : s ≤ T := by
    dsimp [T]
    have H : 0 < 2 * k * Real.log (4 * k) := by positivity
    linarith
  have hE : |coreEnergy (β s 0) (β s 2) - k ^ 2| < 1 / 8 := by
    rw [← coreRadius_sq, hR, sub_self, abs_zero]
    norm_num
  have hP : 0 ≤ β s 2 * β s 3 ∧ β s 2 * β s 3 ≤ (1 / 10000) / k := by
    simpa only [hV, one_mul] using hW
  obtain ⟨r₀, hr₀, hprefix⟩ := normalized_core_local_prefix hc hk hs hA hE (Or.inr ⟨hV, hM⟩) hU hP
  have hsS : s ∈ S := ⟨(hprefix s ⟨le_rfl, hr₀.le⟩).1.le, (hprefix s ⟨le_rfl, hr₀.le⟩).2⟩
  by_contra hnone
  have hwhole : Icc s T ⊆ S := by
    apply (isClosed_normalized_core_times hc hk hs).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hsS
    intro t ht hbefore
    have htS := hbefore ⟨ht.1, le_rfl⟩
    have hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0 := hc0.trans_le htS.1
    have hAbefore (u : ℝ) (hu : u ∈ Icc s t) : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
      hc0.trans_le (hbefore hu).1
    have henergy := (normalized_core_energy_band_improves hc hk hs ht.1 hAbefore hR hV
      (fun u hu => by rw [coreRadius_sq]; exact (hbefore hu).2.1)
      (fun u hu => (hbefore hu).2.2.1) (fun u hu => (hbefore hu).2.2.2.1)
      (fun u hu => (hbefore hu).2.2.2.2)).2
    have hstrict : |coreEnergy (β t 0) (β t 2) - k ^ 2| < 1 / 8 := by
      rw [coreRadius_sq] at henergy
      linarith
    have hvcase : 1 < β t 2 ∨ (β t 2 = 1 ∧ 1 ≤ β t 0) := by
      rcases eq_or_lt_of_le ht.1 with heq | hst
      · subst t
        exact Or.inr ⟨hV, hM⟩
      · left
        apply lt_of_le_of_ne htS.2.2.1
        intro heq
        exact hnone ⟨t, hst, heq.symm, fun u hu => hbefore hu⟩
    obtain ⟨r, htr, hafter⟩ := normalized_core_local_prefix hc hk (hs.trans ht.1) hAt hstrict hvcase
      htS.2.2.2.1 htS.2.2.2.2
    apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
    exact ⟨r, htr, fun u hu => ⟨(hafter u ⟨hu.1.le, hu.2⟩).1.le, (hafter u ⟨hu.1.le, hu.2⟩).2⟩⟩
  have H := (normalized_core_residence hc hk hs hsT (fun u hu => hc0.trans_le (hwhole hu).1)
    (fun u hu => coreRegion_radius_bounds hk (hwhole hu).2)
    (fun u hu => (hwhole hu).2.2.1)
    (fun u hu => (coreRegion_wall_bounds (hwhole hu).2).1)
    (fun u hu => (coreRegion_wall_bounds (hwhole hu).2).2)).2
  dsimp [T] at H
  linarith
