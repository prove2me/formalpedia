-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_one_derivative_bound_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:02:15.788622+00:00
-- url     : https://prove2.me/submissions/40fd615e-b2a9-4bff-93c9-7b0932918205

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (W : ℝ → ℝ) (a x : ℝ)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a))
    (hx : x ∈ Ioo 0 a) :
    ∃ r C : ℝ,
      0 < r ∧ r ≤ min x 1 ∧ 0 ≤ C ∧
      (∀ z : ℝ, z ∈ Icc (x - r) x → |deriv W z| ≤ C) ∧
      (∀ y : ℝ, y ∈ Ioo (-r) 0 → |W (x + y) - W x| ≤ C * |y|) := by
  let r : ℝ := min x 1 / 2
  have hm : 0 < min x 1 := lt_min hx.1 one_pos
  have hr : 0 < r := by dsimp [r]; linarith
  have hrle : r ≤ min x 1 := by dsimp [r]; linarith
  have hrlt : r < min x 1 := by dsimp [r]; linarith
  have hrx : r < x := lt_of_lt_of_le hrlt (min_le_left x 1)
  let K : Set ℝ := Icc (x - r) x
  have hKsub : K ⊆ Ioo 0 a := by
    intro z hz
    exact ⟨lt_of_lt_of_le (sub_pos.mpr hrx) hz.1,
      lt_of_le_of_lt hz.2 hx.2⟩
  have huniq : UniqueDiffOn ℝ K := by
    dsimp [K]
    exact uniqueDiffOn_Icc (by linarith)
  have hcontWithin :
      ContinuousOn (fun z => ‖iteratedDerivWithin 1 W K z‖) K := by
    exact (ContDiffOn.continuousOn_iteratedDerivWithin
      (hC1.mono hKsub) (by norm_num) huniq).norm
  have hcont : ContinuousOn (fun z => |deriv W z|) K := by
    apply hcontWithin.congr
    intro z hz
    have hzC1 : ContDiffAt ℝ 1 W z :=
      hC1.contDiffAt (isOpen_Ioo.mem_nhds (hKsub hz))
    change |deriv W z| = ‖iteratedDerivWithin 1 W K z‖
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq hzC1 hz]
    simp [iteratedDeriv_one, Real.norm_eq_abs]
  have hKne : K.Nonempty := ⟨x, by constructor <;> linarith [hr]⟩
  obtain ⟨zM, hzM, hmax⟩ :
      ∃ zM ∈ K, ∀ z ∈ K, |deriv W z| ≤ |deriv W zM| :=
    isCompact_Icc.exists_isMaxOn hKne hcont
  let C : ℝ := |deriv W zM|
  have hC : 0 ≤ C := abs_nonneg _
  have hdiff : ∀ z ∈ K, DifferentiableAt ℝ W z := by
    intro z hz
    exact (hC1.contDiffAt (isOpen_Ioo.mem_nhds (hKsub hz))).differentiableAt (by norm_num)
  refine ⟨r, C, hr, hrle, hC, (by intro z hz; exact hmax z hz), ?_⟩
  intro y hy
  have hxyK : x + y ∈ K := by
    constructor <;> linarith [hy.1, hy.2]
  have hxK : x ∈ K := by
    constructor <;> linarith [hr]
  have hb : ‖W (x + y) - W x‖ ≤ C * ‖(x + y) - x‖ :=
    (convex_Icc (x - r) x).norm_image_sub_le_of_norm_deriv_le
      hdiff (by intro z hz; simpa [Real.norm_eq_abs, C] using hmax z hz)
      hxK hxyK
  simpa only [Real.norm_eq_abs, add_sub_cancel_left] using hb
