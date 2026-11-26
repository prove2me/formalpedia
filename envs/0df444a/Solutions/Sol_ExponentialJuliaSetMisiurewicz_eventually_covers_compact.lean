-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.eventually_covers_compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:14:48.265822+00:00
-- url     : https://prove2.me/submissions/44a9d8ce-fece-4f03-a139-70881dc99f4c

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
import Definitions.Def_ExpChaotic_Covering
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_covers_compact_of_real_ball
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_exists_re_gt_four_of_real
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_real_orbit
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_isOpen_image_expIterate
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma6_every_domain_eventually_meets_real_axis
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {U K : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ N : ℕ, ∀ n ≥ N, K ⊆ expIterate n '' U := by
  obtain ⟨c, hc⟩ := hUne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU c hc
  have hconn : IsConnected (ball c r) :=
    ⟨⟨c, Metric.mem_ball_self hr⟩, (convex_ball c r).isPreconnected⟩
  -- First reach the real axis, then advance to a real point where disk expansion applies.
  obtain ⟨m, a, ha, hreal⟩ := lemma6_every_domain_eventually_meets_real_axis
    isOpen_ball hconn ⟨c, Metric.mem_ball_self hr⟩
  obtain ⟨j, hj⟩ := exists_re_gt_four_of_real hreal
  let x : ℂ := expIterate j (expIterate m a)
  have hx : x.im = 0 := (expIterate_real_orbit hreal j).1
  have hxmem : x ∈ expIterate (j + m) '' U :=
    ⟨a, hball ha, Function.iterate_add_apply exponentialMap j m a⟩
  -- Openness supplies a disk about that image point; its covering property pulls back to U.
  obtain ⟨s, hs, hsmall⟩ := Metric.isOpen_iff.mp (isOpen_image_expIterate hU (j + m)) x hxmem
  obtain ⟨N, hN⟩ := eventually_covers_compact_of_real_ball hK hK0 hx (by dsimp [x]; linarith) hs
  refine ⟨N + (j + m), fun n hn w hw => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨b, hb, hbw⟩ := hN (N + k) (Nat.le_add_right _ _) hw
  obtain ⟨z, hz, hzb⟩ := hsmall hb
  refine ⟨z, hz, ?_⟩
  calc
    expIterate (N + (j + m) + k) z = expIterate (N + k) (expIterate (j + m) z) := by
      rw [show N + (j + m) + k = (N + k) + (j + m) by omega]
      exact Function.iterate_add_apply exponentialMap (N + k) (j + m) z
    _ = w := by rw [hzb, hbw]
end ExponentialJuliaSetMisiurewicz
