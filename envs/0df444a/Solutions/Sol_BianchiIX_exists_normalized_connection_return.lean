-- Prove2me | solution 1 for BianchiIX.exists_normalized_connection_return
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:11:25.771332+00:00
-- url     : https://prove2.me/submissions/8ffcb7d4-bfe9-44c4-a81e-5d6569a54cce

import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ConnectionRegion
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Theorems.Thm_BianchiIX_isClosed_normalized_connection_times
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_connection_local_prefix
import Theorems.Thm_BianchiIX_normalized_connection_phase_band_improves
import Theorems.Thm_BianchiIX_normalized_connection_residence
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
import Mathlib.Topology.Order.IntermediateValue

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

/-- The actual flow reaches the next wall while remaining in the closed connection region. -/
theorem solution {x : NormalizedState} {t₀ s μ : ℝ}
    (hc : stateConstraint x = 1) (hμ : 4 ≤ μ) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u);
    -β s 0 = μ → β s 2 = 1 →
    (0 ≤ β s 1 ∧ β s 1 ≤ 1 / 10000) → (0 < β s 3 ∧ β s 3 < 1) →
    ∃ t > s, β t 3 = 1 ∧ ∀ u ∈ Icc s t,
      3 / (2 * μ ^ 2) ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ connectionRegion μ (β u) := by
  intro β hM hV hU hW
  have hμ0 : 0 < μ := by linarith only [hμ]
  let c := 3 / (2 * μ ^ 2)
  have hc0 : 0 < c := by dsimp [c]; positivity
  let S : Set ℝ := {u | c ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ connectionRegion μ (β u)}
  let T := s + μ * Real.log (1 / β s 3) + 1
  have hlog : 0 ≤ Real.log (1 / β s 3) := by
    rw [one_div, Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hW.1.le hW.2.le)
  have hsT : s ≤ T := by
    dsimp [T]
    nlinarith only [mul_nonneg hμ0.le hlog]
  have hm : |-β s 0 - μ| < 1 / 2 := by rw [hM, sub_self, abs_zero]; norm_num
  have hv : 0 < β s 2 ∧ β s 2 ≤ 1 := by rw [hV]; norm_num
  have hentry : β s 1 ≤ β s 2 := by rw [hV]; linarith only [hU.2]
  obtain ⟨r₀, hr₀, hprefix⟩ := normalized_connection_local_prefix hc hμ hs hA hm hU hv hW
  have hsS : s ∈ S := ⟨(hprefix s ⟨le_rfl, hr₀.le⟩).1.le, (hprefix s ⟨le_rfl, hr₀.le⟩).2⟩
  have hdom (u : ℝ) (hu : s ≤ u) : u ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu)
  have hpositive (u : ℝ) (hu : s ≤ u) (hAu : 0 < 1 + normalizedMaxCurve x t₀ u 0) :
      0 < β u 2 ∧ 0 < β u 3 :=
    ⟨normalized_projective_wall_pos (hdom s le_rfl) (hdom u hu) hA hAu 1 hv.1,
      normalized_projective_wall_pos (hdom s le_rfl) (hdom u hu) hA hAu 2 hW.1⟩
  by_contra hnone
  have hwhole : Icc s T ⊆ S := by
    apply (isClosed_normalized_connection_times hc hμ hs).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hsS
    intro t ht hbefore
    have htS := hbefore ⟨ht.1, le_rfl⟩
    have hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0 := hc0.trans_le htS.1
    have hAbefore (u : ℝ) (hu : u ∈ Icc s t) : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
      hc0.trans_le (hbefore hu).1
    have hpos (u : ℝ) (hu : u ∈ Icc s t) := hpositive u hu.1 (hAbefore u hu)
    have hstrict := (normalized_connection_phase_band_improves hc hμ hs ht.1 hAbefore hM
      (fun u hu => (hbefore hu).2.1) (fun u hu => (hbefore hu).2.2.1)
      (fun u hu => ⟨(hpos u hu).1, (hbefore hu).2.2.2.1.2⟩)
      (fun u hu => ⟨(hpos u hu).2, (hbefore hu).2.2.2.2.2⟩) hentry).2
    have hwlt : β t 3 < 1 := by
      rcases eq_or_lt_of_le ht.1 with heq | hst
      · subst t
        exact hW.2
      · apply lt_of_le_of_ne htS.2.2.2.2.2
        intro heq
        exact hnone ⟨t, hst, heq, fun u hu => hbefore hu⟩
    obtain ⟨r, htr, hafter⟩ := normalized_connection_local_prefix hc hμ (hs.trans ht.1) hAt
      hstrict htS.2.2.1 ⟨(hpositive t ht.1 hAt).1, htS.2.2.2.1.2⟩
      ⟨(hpositive t ht.1 hAt).2, hwlt⟩
    apply mem_nhdsGT_iff_exists_Ioc_subset.mpr
    exact ⟨r, htr, fun u hu => ⟨(hafter u ⟨hu.1.le, hu.2⟩).1.le, (hafter u ⟨hu.1.le, hu.2⟩).2⟩⟩
  have H := (normalized_connection_residence hc hμ hs hsT
    (fun u hu => hc0.trans_le (hwhole hu).1) (fun u hu => (hwhole hu).2)
    (fun u hu => (hpositive u hu.1 (hc0.trans_le (hwhole hu).1)).2)).2
  dsimp [T] at H
  linarith only [H]
