-- Prove2me | solution 1 for AvramDividend.Classical.deriv_bounded_on_compact_of_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:48:53.120985+00:00
-- url     : https://prove2.me/submissions/e1cb1d38-7a1d-435d-9b75-064273ef3b36

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ) (a l u : ℝ)
    (hlu : l < u) (hsub : Icc l u ⊆ Ioo 0 a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc l u, |deriv W x| ≤ C := by
  have hC1K : ContDiffOn ℝ 1 W (Icc l u) := hC1.mono hsub
  have huniq : UniqueDiffOn ℝ (Icc l u) :=
    uniqueDiffOn_Icc hlu
  have hcont :
      ContinuousOn
        (fun z => ‖iteratedDerivWithin 1 W (Icc l u) z‖)
        (Icc l u) := by
    exact (ContDiffOn.continuousOn_iteratedDerivWithin
      hC1K (by norm_num) huniq).norm
  have hKne : (Icc l u).Nonempty :=
    ⟨l, ⟨le_rfl, hlu.le⟩⟩
  obtain ⟨zM, hzM, hmax⟩ :
      ∃ zM ∈ Icc l u, ∀ z ∈ Icc l u,
        ‖iteratedDerivWithin 1 W (Icc l u) z‖ ≤
          ‖iteratedDerivWithin 1 W (Icc l u) zM‖ :=
    isCompact_Icc.exists_isMaxOn hKne hcont
  let C : ℝ := ‖iteratedDerivWithin 1 W (Icc l u) zM‖
  refine ⟨C, norm_nonneg _, ?_⟩
  intro x hx
  have hxC1 : ContDiffAt ℝ 1 W x :=
    hC1.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))
  have hxEq :
      iteratedDerivWithin 1 W (Icc l u) x = deriv W x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq hxC1 hx]
    simp
  have hn : ‖deriv W x‖ ≤ C := by
    rw [← hxEq]
    exact hmax x hx
  simpa only [Real.norm_eq_abs] using hn
