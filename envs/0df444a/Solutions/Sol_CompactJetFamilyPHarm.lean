-- Prove2me | solution 1 for CompactJetFamilyPHarm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:22:15.255813+00:00
-- url     : https://prove2.me/submissions/c54e7a76-87b4-4b73-8629-e6a5be665ef7

import Definitions.Def_PHigherOrder_CompactJetFamily
import Definitions.Def_PHigherOrder_PHarmJetEquicontinuity
import Definitions.Def_PHigherOrder_PHarmWeakGradClassical
import Definitions.Def_PHigherOrder_PHarmLimit
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_PHarmClassicalGradient
import Definitions.Def_PHigherOrder_CompactJetFamilyPHarm
import Theorems.Thm_PHarmClassicalGradient
import Theorems.Thm_PHarmJetEquicontinuity
import Theorems.Thm_PHarmLimit
import Theorems.Thm_PHarmRestrict
import Theorems.Thm_PHarmWeakGradClassical


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p)
    (z : BoundedContinuousFunction XHalf (ℝ × Plane))
    (hz : z ∈ CompactJetFamily p) :
    (∀ x : XHalf, (x : Plane) = 0 → (z x).1 = 0) ∧
    (∀ x : XHalf, |(z x).1| ≤ 1) ∧
    ∃ (h : Plane → ℝ) (G : Plane → Plane),
      IsPHarm p (Metric.ball 0 (1 / 2)) h G ∧
      (∀ x : XHalf, h (x : Plane) = (z x).1) ∧
      (∀ x : XHalf, G (x : Plane) = (z x).2) ∧
      Set.EqOn G (gradient h) (Metric.ball (0 : Plane) (1 / 2)) := by
  classical
  -- Step 0: the ball inclusions.
  have hhalf : ∀ x : XHalf, ‖(x : Plane)‖ ≤ 1 / 2 := by
    intro x
    have hx := x.2
    rwa [Metric.mem_closedBall, dist_zero_right] at hx
  have hin1 : ∀ x : XHalf, (x : Plane) ∈ Metric.ball (0 : Plane) 1 := by
    intro x
    rw [Metric.mem_ball, dist_zero_right]
    linarith [hhalf x]
  have hb12 : Metric.ball (0 : Plane) (1 / 2) ⊆ Metric.ball (0 : Plane) 1 :=
    Metric.ball_subset_ball (by norm_num)
  have hb34 : Metric.ball (0 : Plane) (1 / 2) ⊆ Metric.ball (0 : Plane) (3 / 4) :=
    Metric.ball_subset_ball (by norm_num)
  have hbcl : Metric.ball (0 : Plane) (1 / 2) ⊆ Metric.closedBall (0 : Plane) (1 / 2) :=
    Metric.ball_subset_closedBall
  -- Step 1: a sequence of generators converging to `z`, the closure being sequential.
  rw [CompactJetFamily] at hz
  obtain ⟨zs, hmem, htend⟩ := mem_closure_iff_seq_limit.mp hz
  -- Step 2: unpack the generators, once and for all, with choice.
  choose v g hvh hvbd hv0 hvjet using hmem
  -- Convergence in the sup metric IS uniform convergence, and it passes to each component
  -- because the projections are uniformly continuous for the max metric.
  have hjet : TendstoUniformly (fun n => ((zs n : BoundedContinuousFunction XHalf (ℝ × Plane)) :
      XHalf → ℝ × Plane)) (z : XHalf → ℝ × Plane) Filter.atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp htend
  have h1 : TendstoUniformly (fun n (x : XHalf) => ((zs n) x).1) (fun x : XHalf => (z x).1)
      Filter.atTop := uniformContinuous_fst.comp_tendstoUniformly hjet
  have h2 : TendstoUniformly (fun n (x : XHalf) => ((zs n) x).2) (fun x : XHalf => (z x).2)
      Filter.atTop := uniformContinuous_snd.comp_tendstoUniformly hjet
  -- Step 4: the extensions off the closed half-ball.  They are introduced as OPAQUE locals
  -- with defining equations, so that the agreement identities hold by construction and
  -- `PHarmLimit` and `PHarmClassicalGradient` can take them as their explicit limits.
  obtain ⟨hfun, hfdef⟩ : ∃ f : Plane → ℝ, f = fun y =>
      if hy : y ∈ Metric.closedBall (0 : Plane) (1 / 2) then (z ⟨y, hy⟩).1 else 0 := ⟨_, rfl⟩
  obtain ⟨Gfun, hGdef⟩ : ∃ f : Plane → Plane, f = fun y =>
      if hy : y ∈ Metric.closedBall (0 : Plane) (1 / 2) then (z ⟨y, hy⟩).2 else 0 := ⟨_, rfl⟩
  have hagree1 : ∀ x : XHalf, hfun (x : Plane) = (z x).1 := by
    intro x
    rw [hfdef]
    show (if hy : (x : Plane) ∈ Metric.closedBall (0 : Plane) (1 / 2) then
      (z ⟨(x : Plane), hy⟩).1 else 0) = (z x).1
    rw [dif_pos x.2]
  have hagree2 : ∀ x : XHalf, Gfun (x : Plane) = (z x).2 := by
    intro x
    rw [hGdef]
    show (if hy : (x : Plane) ∈ Metric.closedBall (0 : Plane) (1 / 2) then
      (z ⟨(x : Plane), hy⟩).2 else 0) = (z x).2
    rw [dif_pos x.2]
  -- Step 5: the convergence already holds on all of the closed half-ball, so restricting to a
  -- compact subset of the OPEN half-ball is the only work.
  have hconvU : ∀ K : Set Plane, K ⊆ Metric.ball (0 : Plane) (1 / 2) → IsCompact K →
      TendstoUniformlyOn (fun n => v n) hfun Filter.atTop K := by
    intro K hK _
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rw [Metric.tendstoUniformly_iff] at h1
    filter_upwards [h1 ε hε] with n hn y hy
    have hyc : y ∈ Metric.closedBall (0 : Plane) (1 / 2) := hbcl (hK hy)
    have key : dist ((z (⟨y, hyc⟩ : XHalf)).1) (((zs n) (⟨y, hyc⟩ : XHalf)).1) < ε := hn ⟨y, hyc⟩
    have e1 : hfun y = (z (⟨y, hyc⟩ : XHalf)).1 := hagree1 ⟨y, hyc⟩
    have e2 : v n y = ((zs n) (⟨y, hyc⟩ : XHalf)).1 := by rw [hvjet n ⟨y, hyc⟩]
    rw [e1, e2]
    exact key
  have hconvG : ∀ K : Set Plane, K ⊆ Metric.ball (0 : Plane) (1 / 2) → IsCompact K →
      TendstoUniformlyOn (fun n => gradient (v n)) Gfun Filter.atTop K := by
    intro K hK _
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rw [Metric.tendstoUniformly_iff] at h2
    filter_upwards [h2 ε hε] with n hn y hy
    have hyc : y ∈ Metric.closedBall (0 : Plane) (1 / 2) := hbcl (hK hy)
    have key : dist ((z (⟨y, hyc⟩ : XHalf)).2) (((zs n) (⟨y, hyc⟩ : XHalf)).2) < ε := hn ⟨y, hyc⟩
    have e1 : Gfun y = (z (⟨y, hyc⟩ : XHalf)).2 := hagree2 ⟨y, hyc⟩
    have e2 : gradient (v n) y = ((zs n) (⟨y, hyc⟩ : XHalf)).2 := by rw [hvjet n ⟨y, hyc⟩]
    rw [e1, e2]
    exact key
  -- Step 6, in the order (a) restrict, (b) `C^1`, (c) bridge to the classical gradient.
  -- Without (c) the generating condition supplies only the arbitrary weak gradient `g n`,
  -- whereas what converges in Step 5 is the CLASSICAL gradient, so `PHarmLimit` would not apply.
  have hrest : ∀ n, IsPHarm p (Metric.ball (0 : Plane) (1 / 2)) (v n) (g n) := fun n =>
    (PHarmRestrict p hp hp2 (Metric.ball 0 1) (v n) (g n) (hvh n)).1
      (Metric.ball 0 (1 / 2)) Metric.isOpen_ball hb12
  have hR : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  have hR32 : (3 : ℝ) * (1 / 2) / 2 = 3 / 4 := by norm_num
  have hC1 : ∀ n, ContDiffOn ℝ 1 (v n) (Metric.ball (0 : Plane) (1 / 2)) := by
    intro n
    have h := PHarmJetEquicontinuity p hp hp2 F 0 (1 / 2) 1 (by norm_num) (by norm_num)
      (v n) (g n) (by rw [hR]; exact hvh n) (by rw [hR]; exact hvbd n)
    rw [hR32] at h
    exact h.1.mono hb34
  have hclass : ∀ n, IsPHarm p (Metric.ball (0 : Plane) (1 / 2)) (v n) (gradient (v n)) :=
    fun n => (PHarmWeakGradClassical p hp (Metric.ball 0 (1 / 2)) (v n) (g n)
      (hrest n) (hC1 n)).1
  -- Step 7: limit passage.
  have hlim : IsPHarm p (Metric.ball (0 : Plane) (1 / 2)) hfun Gfun :=
    PHarmLimit p hp hp2 (Metric.ball 0 (1 / 2)) v (fun n => gradient (v n)) hfun Gfun
      hclass hconvU hconvG
  -- Step 8: the weak gradient is the classical gradient of `hfun`, pointwise on the open ball.
  have hderiv : ∀ n : ℕ, ∀ y ∈ Metric.ball (0 : Plane) (1 / 2),
      HasGradientAt (v n) (gradient (v n) y) y := by
    intro n y hy
    exact (((hC1 n).differentiableOn one_ne_zero).differentiableAt
      (Metric.isOpen_ball.mem_nhds hy)).hasGradientAt
  have hptwise : ∀ y ∈ Metric.ball (0 : Plane) (1 / 2),
      Filter.Tendsto (fun n => v n y) Filter.atTop (nhds (hfun y)) := fun y hy =>
    (hconvU {y} (Set.singleton_subset_iff.mpr hy) isCompact_singleton).tendsto_at rfl
  have hcg := PHarmClassicalGradient (Metric.ball 0 (1 / 2)) Metric.isOpen_ball v
    (fun n => gradient (v n)) hfun Gfun hderiv hconvG hptwise
  refine ⟨?_, ?_, hfun, Gfun, hlim, hagree1, hagree2, fun y hy => (hcg y hy).2.symm⟩
  · -- Part (a):  a constant sequence has that constant as its limit.
    intro x hx0
    have hta : Filter.Tendsto (fun n => ((zs n) x).1) Filter.atTop (nhds ((z x).1)) :=
      h1.tendsto_at x
    have hconst : ∀ n, ((zs n) x).1 = 0 := by
      intro n
      rw [hvjet n x]
      show v n (x : Plane) = 0
      rw [hx0]
      exact hv0 n
    have hc : Filter.Tendsto (fun n => ((zs n) x).1) Filter.atTop (nhds 0) := by
      simp only [hconst]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hta hc
  · -- Part (b):  a weak inequality passes to the limit.
    intro x
    have hta : Filter.Tendsto (fun n => ((zs n) x).1) Filter.atTop (nhds ((z x).1)) :=
      h1.tendsto_at x
    refine le_of_tendsto' hta.abs ?_
    intro n
    rw [hvjet n x]
    show |v n (x : Plane)| ≤ 1
    exact hvbd n (x : Plane) (hin1 x)
