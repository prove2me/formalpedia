-- Prove2me | solution 1 for BianchiIX.exists_normalized_entrance_arrival
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:04:21.527026+00:00
-- url     : https://prove2.me/submissions/557df43f-809b-4793-baf8-abdd34fced61

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_EntranceRegion
import Theorems.Thm_BianchiIX_isClosed_normalized_entrance_times
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_entrance_local_prefix
import Theorems.Thm_BianchiIX_normalized_entrance_radius_improves
import Theorems.Thm_BianchiIX_normalized_entrance_residence
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
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
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

theorem solution {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 7 / 4 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < normalizedProjectiveRate x t₀ s) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    1 ≤ Y s 0 → coreRadius (Y s 0) (Y s 2) = k →
    (0 ≤ Y s 1 ∧ Y s 1 ≤ 1 / 10000) → (0 < Y s 2 ∧ Y s 2 < 1) →
    (0 ≤ Y s 3 ∧ Y s 3 ≤ 1 / 10000) →
    ∃ t > s, Y t 2 = 1 ∧ ∀ r ∈ Icc s t,
      1 / (2 * (k + 1) ^ 2) ≤ normalizedProjectiveRate x t₀ r ∧ entranceRegion k (Y r) := by
  intro Y hm hR hu hv hw
  have hk0 : 0 < k := by linarith
  have hK : 0 < k + 1 := by linarith
  let c := 1 / (2 * (k + 1) ^ 2)
  have hc0 : 0 < c := by dsimp [c]; positivity
  let S : Set ℝ := {r | c ≤ normalizedProjectiveRate x t₀ r ∧ entranceRegion k (Y r)}
  let T := s + (2 * (k + 1) ^ 2 / k) * Real.log (1 / Y s 2) + 1
  have hlog : 0 ≤ Real.log (1 / Y s 2) := by
    rw [one_div, Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hsT : s ≤ T := by
    dsimp [T]
    nlinarith only [mul_nonneg (show 0 ≤ 2 * (k + 1) ^ 2 / k by positivity) hlog]
  have hRstrict : |coreRadius (Y s 0) (Y s 2) - k| < k / 100 := by rw [hR, sub_self, abs_zero]; positivity
  obtain ⟨r₀, hr₀, hprefix⟩ := normalized_entrance_local_prefix hc hk hs hA hm hRstrict hu hv hw
  have hsS : s ∈ S := ⟨(hprefix s ⟨le_rfl, hr₀.le⟩).1.le, (hprefix s ⟨le_rfl, hr₀.le⟩).2⟩
  have hdom (r : ℝ) (hr : s ≤ r) := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hr)
  have hpositive (r : ℝ) (hr : s ≤ r) (hAr : 0 < normalizedProjectiveRate x t₀ r) : 0 < Y r 2 :=
    normalized_projective_wall_pos (hdom s le_rfl) (hdom r hr) hA hAr 1 hv.1
  by_contra hnone
  have hwhole : Icc s T ⊆ S := by
    apply (isClosed_normalized_entrance_times hc hk hs).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hsS
    intro t ht hbefore
    have htS := hbefore ⟨ht.1, le_rfl⟩
    have hAt : 0 < normalizedProjectiveRate x t₀ t := hc0.trans_le htS.1
    have hAbefore (r : ℝ) (hr : r ∈ Icc s t) : 0 < normalizedProjectiveRate x t₀ r := hc0.trans_le (hbefore hr).1
    have hstrict := (normalized_entrance_radius_improves hc hk hs ht.1 hAbefore
      (fun r hr => (hbefore hr).2) hv.1 hR).2
    have hvlt : Y t 2 < 1 := by
      rcases eq_or_lt_of_le ht.1 with heq | hst
      · subst t; exact hv.2
      · apply lt_of_le_of_ne htS.2.2.2.2.1.2
        intro heq
        exact hnone ⟨t, hst, heq, fun r hr => hbefore hr⟩
    obtain ⟨r, htr, hafter⟩ := normalized_entrance_local_prefix hc hk (hs.trans ht.1) hAt htS.2.1
      (hstrict.trans (by linarith)) htS.2.2.2.1 ⟨hpositive t ht.1 hAt, hvlt⟩ htS.2.2.2.2.2
    apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
    exact ⟨r, htr, fun b hb => ⟨(hafter b ⟨hb.1.le, hb.2⟩).1.le, (hafter b ⟨hb.1.le, hb.2⟩).2⟩⟩
  have H := (normalized_entrance_residence hc hk hs hsT
    (fun r hr => hc0.trans_le (hwhole hr).1) (fun r hr => (hwhole hr).2) hv.1).2
  dsimp [T] at H
  linarith only [H]
