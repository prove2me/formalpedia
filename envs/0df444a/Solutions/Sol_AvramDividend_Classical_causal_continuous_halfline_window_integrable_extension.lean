-- Prove2me | solution 1 for AvramDividend.Classical.causal_continuous_halfline_window_integrable_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:09:36.832362+00:00
-- url     : https://prove2.me/submissions/6b59973c-44f5-48d5-883e-bcedcb1d0dee

import Mathlib.Topology.ContinuousOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Preserve a finite positive-time window under a continuous L1 taper. -/
theorem solution
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (R : ℝ) (hR : 0 < R) :
    ∃ F : ℝ → ℝ,
      ContinuousOn F (Ici (0 : ℝ)) ∧
      IntegrableOn F (Ioi (0 : ℝ)) volume ∧
      (∀ t ∈ Icc (0 : ℝ) R, F t = f t) := by
  let F : ℝ → ℝ := fun t =>
    f (min t R) * max (0 : ℝ) (min 1 (R + 1 - t))
  have hmincont : Continuous (fun t : ℝ => min t R) :=
    continuous_id.min continuous_const
  have hminmem : ∀ t ∈ Ici (0 : ℝ), min t R ∈ Ici (0 : ℝ) := by
    intro t ht
    exact le_min (mem_Ici.mp ht) hR.le
  have hfmin : ContinuousOn (fun t : ℝ => f (min t R)) (Ici (0 : ℝ)) :=
    hf.comp hmincont.continuousOn hminmem
  have htaper : Continuous
      (fun t : ℝ => max (0 : ℝ) (min 1 (R + 1 - t))) := by
    fun_prop
  have hFcont : ContinuousOn F (Ici (0 : ℝ)) :=
    hfmin.mul htaper.continuousOn
  have hFcompact : IntegrableOn F (Icc (0 : ℝ) (R + 1)) volume := by
    apply ContinuousOn.integrableOn_Icc
    exact hFcont.mono (by intro t ht; exact ht.1)
  have hFint : IntegrableOn F (Ioi (0 : ℝ)) volume := by
    apply hFcompact.of_forall_sdiff_eq_zero measurableSet_Ioi
    intro t ht
    have htpos : 0 < t := mem_Ioi.mp ht.1
    have hupper : R + 1 ≤ t := by
      by_contra hn
      have hmem : t ∈ Icc (0 : ℝ) (R + 1) :=
        ⟨htpos.le, le_of_not_ge hn⟩
      exact ht.2 hmem
    have hneg : min (1 : ℝ) (R + 1 - t) ≤ 0 :=
      (min_le_right 1 (R + 1 - t)).trans (by linarith)
    change f (min t R) * max 0 (min 1 (R + 1 - t)) = 0
    rw [max_eq_left hneg]
    ring
  refine ⟨F, hFcont, hFint, ?_⟩
  intro t ht
  have hmin : min t R = t := min_eq_left ht.2
  have hone : min (1 : ℝ) (R + 1 - t) = 1 :=
    min_eq_left (by linarith [ht.2])
  have hmax : max (0 : ℝ) (min 1 (R + 1 - t)) = 1 := by
    rw [hone]
    norm_num
  simp only [F, hmin, hmax, mul_one]
