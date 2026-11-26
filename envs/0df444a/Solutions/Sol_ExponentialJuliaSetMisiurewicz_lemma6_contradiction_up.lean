-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma6_contradiction_up
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:21.001932+00:00
-- url     : https://prove2.me/submissions/513c53bb-e617-4783-ae8e-725356cc4468

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_ExpChaotic_HalfPlane
import Definitions.Def_ExpChaotic_RealAxis
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_re_gt_four_of_real
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma6_accumulation_up
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_isClosed_centralStrip
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_isOpen_rightHalfPlane
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_continuous_expIterate
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma2b_eventually_leaves_strip
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma4_eventually_meets_centralStrip
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma5_real_axis_of_frequently_in_rightHalfPlane


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {V : Set ℂ} (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0)
    {T : Set ℕ} (hTinf : T.Infinite)
    (hTup : ∀ n ∈ T, ∀ z ∈ V, 0 < (expIterate n z).im) :
    False := by
  obtain ⟨p, y, hpim, haccum⟩ := lemma6_accumulation_up hVopen hVne hnoreal hTinf hTup
  by_cases hpreal : p.im = 0
  · -- `p` is real: its orbit escapes to the right, so Lemma 5 applies
    obtain ⟨m, hm⟩ := exists_re_gt_four_of_real hpreal
    obtain ⟨η, hη, hηball⟩ := Metric.isOpen_iff.mp
      (isOpen_rightHalfPlane.preimage (continuous_expIterate m)) p hm
    obtain ⟨δ, hδ, hsubV, hinf⟩ := haccum η hη
    have hballconn : IsConnected (ball y δ) :=
      ⟨⟨y, Metric.mem_ball_self hδ⟩, (convex_ball y δ).isPreconnected⟩
    have hmaps : {N : ℕ | MapsTo (expIterate N) (ball y δ) rightHalfPlane}.Infinite := by
      apply Set.infinite_of_not_bddAbove
      rintro ⟨M, hM⟩
      obtain ⟨n, hn, hz⟩ := hinf (M + 1)
      have hmem : (m + n) ∈ {N : ℕ | MapsTo (expIterate N) (ball y δ) rightHalfPlane} := by
        intro z hzmem
        have h2 : expIterate n z ∈ ball p η := by
          rw [Metric.mem_ball, dist_eq_norm]; exact hz z hzmem
        have heq : expIterate (m + n) z = expIterate m (expIterate n z) :=
          Function.iterate_add_apply _ _ _ _
        rw [heq]
        exact hηball h2
      have hle := hM hmem
      omega
    obtain ⟨N, z, hz, hval⟩ := lemma5_real_axis_of_frequently_in_rightHalfPlane
      isOpen_ball hballconn ⟨y, Metric.mem_ball_self hδ⟩ hmaps
    exact hnoreal N z (hsubV hz) hval
  · -- `p` is not real: its orbit leaves the strip, contradicting Lemma 4
    obtain ⟨m, hm⟩ := lemma2b_eventually_leaves_strip (show ¬ OnRealAxis p from hpreal)
    obtain ⟨η, hη, hηball⟩ := Metric.isOpen_iff.mp
      (isClosed_centralStrip.isOpen_compl.preimage (continuous_expIterate m)) p hm
    obtain ⟨δ, hδ, hsubV, hinf⟩ := haccum η hη
    have hballconn : IsConnected (ball y δ) :=
      ⟨⟨y, Metric.mem_ball_self hδ⟩, (convex_ball y δ).isPreconnected⟩
    obtain ⟨N4, hN4⟩ := lemma4_eventually_meets_centralStrip isOpen_ball hballconn
      ⟨y, Metric.mem_ball_self hδ⟩
    obtain ⟨n, hn, hz⟩ := hinf N4
    obtain ⟨x, ⟨u, hu, rfl⟩, hxs⟩ := hN4 (m + n) (by omega)
    have h2 : expIterate n u ∈ ball p η := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hz u hu
    have heq : expIterate (m + n) u = expIterate m (expIterate n u) :=
      Function.iterate_add_apply _ _ _ _
    rw [heq] at hxs
    exact hηball h2 hxs
end ExponentialJuliaSetMisiurewicz
