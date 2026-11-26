-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma5_negative_real_axis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:17.905056+00:00
-- url     : https://prove2.me/submissions/ac7c947d-a375-4d1a-bf99-01b4c205f0e3

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma4_eventually_meets_centralStrip
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_IsPreconnected_inter_frontier_nonempty
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_rightHalfPlane_exp_of_mem
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_isOpen_image_expIterate
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_neg_real_of_abs_im_eq_pi
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_frontier_piStrip_subset
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_frontier_expPiStrip_subset
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_disjoint_frontier_centralStrip_pi
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_continuous_expIterate
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma2b_eventually_leaves_strip
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {V : Set ℂ} (hVopen : IsOpen V) (hVconn : IsConnected V) (hVne : V.Nonempty)
    (hfrequent : Set.Infinite {n : ℕ | MapsTo (expIterate n) V rightHalfPlane}) :
    EventuallyMeetsNegativeRealAxis V := by
  by_contra hcon
  have hnoneg : ∀ (n : ℕ), ∀ z ∈ V,
      ¬ ((expIterate n z).im = 0 ∧ (expIterate n z).re < 0) := by
    intro n z hz hval
    exact hcon ⟨n, z, hz, hval.1, hval.2⟩
  set W2 : Set ℂ := {z : ℂ | |(Complex.exp z).im| ≤ Real.pi} with hW2
  have himgconn : ∀ n : ℕ, IsPreconnected (expIterate n '' V) := fun n =>
    hVconn.isPreconnected.image _ (continuous_expIterate n).continuousOn
  -- Avoiding the negative axis forces every image to avoid both relevant strip frontiers.
  have hA : ∀ n : ℕ, Disjoint (expIterate n '' V) (frontier piStrip) := by
    intro n
    rw [Set.disjoint_right]
    rintro x hx ⟨z, hz, rfl⟩
    have h2 : |(expIterate n z).im| = Real.pi := frontier_piStrip_subset hx
    obtain ⟨h3, h4⟩ := neg_real_of_abs_im_eq_pi h2
    rw [← expIterate_succ] at h3 h4
    exact hnoneg (n + 1) z hz ⟨h3, h4⟩
  have hB : ∀ n : ℕ, Disjoint (expIterate n '' V) (frontier W2) := by
    intro n
    rw [Set.disjoint_right]
    rintro x hx ⟨z, hz, rfl⟩
    have h2 : |(Complex.exp (expIterate n z)).im| = Real.pi := frontier_expPiStrip_subset hx
    rw [← expIterate_succ] at h2
    obtain ⟨h3, h4⟩ := neg_real_of_abs_im_eq_pi h2
    rw [← expIterate_succ] at h3 h4
    exact hnoneg (n + 2) z hz ⟨h3, h4⟩
  -- A connected image avoiding a frontier lies entirely on one side of it.
  have hdich : ∀ (n : ℕ) (U : Set ℂ), Disjoint (expIterate n '' V) (frontier U) →
      expIterate n '' V ⊆ U ∨ Disjoint (expIterate n '' V) U := by
    intro n U hfr
    by_cases hsub : expIterate n '' V ⊆ U
    · exact Or.inl hsub
    refine Or.inr ?_
    by_contra hdisj
    rw [Set.not_disjoint_iff] at hdisj
    obtain ⟨x, hx1, hx2⟩ := hdisj
    have hdn : (expIterate n '' V \ U).Nonempty := Set.sdiff_nonempty.mpr hsub
    obtain ⟨p, hp1, hp2⟩ :=
      IsPreconnected.inter_frontier_nonempty (himgconn n) ⟨x, hx1, hx2⟩ hdn
    exact Set.disjoint_left.mp hfr hp1 hp2
  obtain ⟨N, hN⟩ := lemma4_eventually_meets_centralStrip hVopen hVconn hVne
  have hpi := Real.pi_pos
  -- Lemma 4 rules out the exterior side for all sufficiently late images.
  have hds : ∀ n, N ≤ n → expIterate n '' V ⊆ piDoubleStrip := by
    intro n hn
    have hsub1 : expIterate n '' V ⊆ piStrip := by
      rcases hdich n piStrip (hA n) with h | h
      · exact h
      · exfalso
        obtain ⟨x, hx1, hx2⟩ := hN n hn
        refine Set.disjoint_left.mp h hx1 ?_
        show |x.im| ≤ Real.pi
        have hx3 : |x.im| ≤ Real.pi / 3 := hx2
        linarith
    have hsub2 : expIterate n '' V ⊆ W2 := by
      rcases hdich n W2 (hB n) with h | h
      · exact h
      · exfalso
        obtain ⟨x, hx1, hx2⟩ := hN (n + 1) (by omega)
        obtain ⟨z, hz, rfl⟩ := hx1
        refine Set.disjoint_left.mp h ⟨z, hz, rfl⟩ ?_
        show |(Complex.exp (expIterate n z)).im| ≤ Real.pi
        rw [← expIterate_succ]
        have hx3 : |(expIterate (n + 1) z).im| ≤ Real.pi / 3 := hx2
        linarith
    exact fun x hx => ⟨hsub1 hx, hsub2 hx⟩
  -- In the right half-plane, the double-strip constraint forces the central-strip constraint.
  have hcs : ∀ k, N ≤ k → expIterate k '' V ⊆ piDoubleStrip ∩ rightHalfPlane →
      expIterate k '' V ⊆ centralStrip := by
    intro k hk hsub
    have hfrdisj : Disjoint (expIterate k '' V) (frontier centralStrip) := by
      rw [Set.disjoint_right]
      intro x hfr hx
      exact Set.disjoint_left.mp disjoint_frontier_centralStrip_pi hfr (hsub hx)
    rcases hdich k centralStrip hfrdisj with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx1, hx2⟩ := hN k hk
      exact Set.disjoint_left.mp h hx1 hx2
  obtain ⟨n, hnmem, hnge⟩ := hfrequent.exists_gt N
  have hnge' : N ≤ n := le_of_lt hnge
  have hmaps : MapsTo (expIterate n) V rightHalfPlane := hnmem
  -- Once an image is far enough right, all its later images would remain in the central strip.
  have hall : ∀ m : ℕ,
      expIterate (n + m) '' V ⊆ piDoubleStrip ∩ rightHalfPlane ∩ centralStrip := by
    intro m
    induction m with
    | zero =>
        have h1 : expIterate (n + 0) '' V ⊆ piDoubleStrip := by
          simpa using hds n hnge'
        have h2 : expIterate (n + 0) '' V ⊆ rightHalfPlane := by
          rintro x ⟨z, hz, rfl⟩
          simpa using hmaps hz
        have h3 := hcs (n + 0) (by omega) (fun x hx => ⟨h1 hx, h2 hx⟩)
        exact fun x hx => ⟨⟨h1 hx, h2 hx⟩, h3 hx⟩
    | succ m ih =>
        have hidx : n + (m + 1) = (n + m) + 1 := by omega
        have h1 : expIterate (n + (m + 1)) '' V ⊆ piDoubleStrip := hds _ (by omega)
        have h2 : expIterate (n + (m + 1)) '' V ⊆ rightHalfPlane := by
          rintro x ⟨z, hz, rfl⟩
          rw [hidx, expIterate_succ]
          have hz1 := ih ⟨z, hz, rfl⟩
          exact rightHalfPlane_exp_of_mem hz1.2 hz1.1.2
        have h3 := hcs _ (by omega : N ≤ n + (m + 1)) (fun x hx => ⟨h1 hx, h2 hx⟩)
        exact fun x hx => ⟨⟨h1 hx, h2 hx⟩, h3 hx⟩
  -- the image is open, so it contains a non-real point, whose orbit cannot stay in the strip
  obtain ⟨z0, hz0⟩ := hVne
  obtain ⟨εb, hεb, hbsub⟩ :=
    Metric.isOpen_iff.mp (isOpen_image_expIterate hVopen n) (expIterate n z0) ⟨z0, hz0, rfl⟩
  have hex : ∃ q ∈ expIterate n '' V, q.im ≠ 0 := by
    have hnormI : ‖Complex.I * ((εb / 2 : ℝ) : ℂ)‖ = εb / 2 := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by positivity)
    by_cases hb : 0 ≤ (expIterate n z0).im
    · refine ⟨expIterate n z0 + Complex.I * ((εb / 2 : ℝ) : ℂ), hbsub ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hnormI]
        linarith
      · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
        exact ne_of_gt (by linarith)
    · push Not at hb
      refine ⟨expIterate n z0 - Complex.I * ((εb / 2 : ℝ) : ℂ), hbsub ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, hnormI]
        linarith
      · simp only [Complex.sub_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
        exact ne_of_lt (by linarith)
  obtain ⟨q, ⟨u, hu, rfl⟩, hqim⟩ := hex
  have hstrip : ∀ m : ℕ, expIterate m (expIterate n u) ∈ centralStrip := by
    intro m
    have hmem := (hall m) ⟨u, hu, rfl⟩
    have heq : expIterate m (expIterate n u) = expIterate (n + m) u := by
      show exponentialMap^[m] (exponentialMap^[n] u) = exponentialMap^[n + m] u
      rw [Nat.add_comm, Function.iterate_add_apply]
    rw [heq]
    exact hmem.2
  obtain ⟨m, hm⟩ := lemma2b_eventually_leaves_strip
    (show ¬ OnRealAxis (expIterate n u) from hqim)
  exact hm (hstrip m)
end ExponentialJuliaSetMisiurewicz
