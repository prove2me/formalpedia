-- Prove2me | solution 1 for FiniteEnergyPlane.norm_sub_sub_linearized_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T15:51:21.649184+00:00
-- url     : https://prove2.me/submissions/88eb507d-e856-42ee-b2e9-33f29ba87121

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitz_near_compact

open Set Metric Filter Topology

/-! Generic analytic helpers for `exists_tubeCoords_near_linearized` (leaf B of K 138fff41). -/


namespace TCBase

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `(ε/K)(e^{Kx} - 1) ≤ ε x e^{Kx}`, packaged as a bound on `gronwallBound`. -/
lemma gronwallBound_le {δ K ε x : ℝ} (hδ : 0 ≤ δ) (hK : 0 < K) (hε : 0 ≤ ε) (hx : 0 ≤ x) :
    gronwallBound δ K ε x ≤ (δ + ε * x) * Real.exp (K * x) := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
    have := Real.add_one_le_exp (-(K * x))
    have hE := Real.exp_pos (K * x)
    have h2 : Real.exp (-(K * x)) * Real.exp (K * x) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith
  have h3 : ε / K * (Real.exp (K * x) - 1) ≤ ε * x * Real.exp (K * x) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK]
    nlinarith [mul_le_mul_of_nonneg_left h1 hε]
  nlinarith

/-- Forward Grönwall on `[0, L]` with an everywhere-derivative hypothesis. -/
lemma gronwall_fwd {f f' : ℝ → E} {L K ε : ℝ} (hK : 0 < K) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hf : ∀ t ∈ Icc (-L) L, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Icc (-L) L, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ∀ t ∈ Icc 0 L, ‖f t‖ ≤ (‖f 0‖ + ε * L) * Real.exp (K * L) := by
  have hsub : Icc 0 L ⊆ Icc (-L) L := Icc_subset_Icc (by linarith) le_rfl
  have hcont : ContinuousOn f (Icc 0 L) := fun t ht =>
    (hf t (hsub ht)).continuousAt.continuousWithinAt
  have key := norm_le_gronwallBound_of_norm_deriv_right_le (f := f) (f' := f') (δ := ‖f 0‖)
    (K := K) (ε := ε) (a := 0) (b := L) hcont
    (fun t ht => (hf t (hsub (Ico_subset_Icc_self ht))).hasDerivWithinAt) le_rfl
    (fun t ht => hb t (hsub (Ico_subset_Icc_self ht)))
  intro t ht
  refine (key t ht).trans ?_
  rw [sub_zero]
  refine (gronwallBound_le (norm_nonneg _) hK hε ht.1).trans ?_
  have h1 : ‖f 0‖ + ε * t ≤ ‖f 0‖ + ε * L := by nlinarith [ht.2]
  have h2 : Real.exp (K * t) ≤ Real.exp (K * L) := Real.exp_le_exp.2 (by nlinarith [ht.2])
  have h3 : 0 ≤ ‖f 0‖ + ε * t := by nlinarith [norm_nonneg (f 0), ht.1]
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by linarith)

/-- Two-sided Grönwall on `[-L, L]`, centred at `0`. -/
lemma gronwall_two {f f' : ℝ → E} {L K ε : ℝ} (hK : 0 < K) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hf : ∀ t ∈ Icc (-L) L, HasDerivAt f (f' t) t)
    (hb : ∀ t ∈ Icc (-L) L, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ∀ t ∈ Icc (-L) L, ‖f t‖ ≤ (‖f 0‖ + ε * L) * Real.exp (K * L) := by
  intro t ht
  rcases le_total 0 t with h0 | h0
  · exact gronwall_fwd hK hε hL hf hb t ⟨h0, ht.2⟩
  · have hg : ∀ s ∈ Icc (-L) L, HasDerivAt (fun s => f (-s)) (-f' (-s)) s := by
      intro s hs
      have hs' : -s ∈ Icc (-L) L := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      exact ((hf (-s) hs').scomp s (hasDerivAt_neg s)).congr_deriv (by simp)
    have hgb : ∀ s ∈ Icc (-L) L, ‖-f' (-s)‖ ≤ K * ‖f (-s)‖ + ε := by
      intro s hs
      rw [norm_neg]
      exact hb (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have := gronwall_fwd (f := fun s => f (-s)) hK hε hL hg hgb (-t) ⟨by linarith, by linarith [ht.1]⟩
    simpa using this

/-- Gronwall with bootstrap (copied from `ROFCore.traj_close`). -/
lemma traj_close {R : E → E} {x Q : ℝ → E} {K : NNReal} {δ : ℝ}
    (hL : ∀ t, LipschitzOnWith K R (ball (x t) δ))
    (hx : ∀ t, HasDerivAt x (R (x t)) t) (hQ : ∀ t, HasDerivAt Q (R (Q t)) t)
    {a b ε : ℝ} (h0 : dist (Q a) (x a) ≤ ε) (hε : ε * Real.exp (K * (b - a)) < δ) :
    ∀ t ∈ Icc a b, dist (Q t) (x t) ≤ ε * Real.exp (K * (t - a)) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hQc : Continuous Q := continuous_iff_continuousAt.2 fun t => (hQ t).continuousAt
  have gron : ∀ c ∈ Icc a b, (∀ t ∈ Ico a c, dist (Q t) (x t) < δ) →
      ∀ t ∈ Icc a c, dist (Q t) (x t) ≤ ε * Real.exp (K * (t - a)) := by
    intro c hc hin
    have hδ : 0 < δ := lt_of_le_of_lt (le_trans dist_nonneg h0 |> fun h =>
      mul_nonneg h (Real.exp_pos _).le) hε
    exact dist_le_of_trajectories_ODE_of_mem (v := fun _ => R) (s := fun t => ball (x t) δ)
      (fun t _ => hL t) hQc.continuousOn (fun t _ => (hQ t).hasDerivWithinAt)
      (fun t ht => mem_ball.2 (hin t ht)) hxc.continuousOn (fun t _ => (hx t).hasDerivWithinAt)
      (fun t _ => mem_ball_self hδ) h0
  have mono : ∀ t ∈ Icc a b, ε * Real.exp (K * (t - a)) < δ := by
    intro t ht
    refine lt_of_le_of_lt ?_ hε
    have hε0 : 0 ≤ ε := le_trans dist_nonneg h0
    gcongr
    exact ht.2
  by_cases hS : ∃ t ∈ Icc a b, δ ≤ dist (Q t) (x t)
  · exfalso
    set S := Icc a b ∩ {t | δ ≤ dist (Q t) (x t)} with hSdef
    have hSc : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const (hQc.dist hxc))
    have hSne : S.Nonempty := by obtain ⟨t, ht, h⟩ := hS; exact ⟨t, ht, h⟩
    have hSb : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
    have hmem := hSc.csInf_mem hSne hSb
    set c := sInf S
    have hc : c ∈ Icc a b := hmem.1
    have hin : ∀ t ∈ Ico a c, dist (Q t) (x t) < δ := by
      intro t ht
      by_contra hcon
      push Not at hcon
      have : c ≤ t := csInf_le hSb ⟨⟨ht.1, ht.2.le.trans hc.2⟩, hcon⟩
      exact absurd ht.2 (not_lt.2 this)
    have := gron c hc hin c ⟨hc.1, le_rfl⟩
    have h2 := mono c hc
    exact absurd hmem.2 (not_le.2 (lt_of_le_of_lt this h2))
  · push Not at hS
    intro t ht
    exact gron b ⟨ht.1.trans ht.2, le_rfl⟩ (fun t ht => hS t ⟨ht.1, ht.2.le⟩) t ht

/-- Two-sided version of `traj_close` on `[-L, L]` for trajectories compared with `x(c + ·)`. -/
lemma traj_close_two {R : E → E} {x Q : ℝ → E} {K : NNReal} {δ : ℝ}
    (hL : ∀ t, LipschitzOnWith K R (ball (x t) δ))
    (hx : ∀ t, HasDerivAt x (R (x t)) t) (hQ : ∀ t, HasDerivAt Q (R (Q t)) t)
    {c L ε : ℝ} (h0 : dist (Q 0) (x c) ≤ ε) (hε : ε * Real.exp (K * L) < δ) :
    ∀ t ∈ Icc (-L) L, dist (Q t) (x (c + t)) ≤ ε * Real.exp (K * L) := by
  have hε0 : 0 ≤ ε := le_trans dist_nonneg h0
  intro t ht
  rcases le_total 0 t with h0t | h0t
  · have hx' : ∀ s, HasDerivAt (fun s => x (c + s)) (R (x (c + s))) s := fun s =>
      (hx (c + s)).comp_const_add c s
    have hL' : ∀ s, LipschitzOnWith K R (ball (x (c + s)) δ) := fun s => hL (c + s)
    have key := traj_close (x := fun s => x (c + s)) hL' hx' hQ (a := 0) (b := L)
      (by simpa using h0) (by simpa using hε) t ⟨h0t, ht.2⟩
    refine key.trans ?_
    gcongr
    · linarith [ht.2]
  · have hx' : ∀ s, HasDerivAt (fun s => x (c - s)) ((-R) (x (c - s))) s := fun s => by
      exact ((hx (c - s)).scomp s ((hasDerivAt_id s).const_sub c)).congr_deriv (by simp)
    have hQ' : ∀ s, HasDerivAt (fun s => Q (-s)) ((-R) (Q (-s))) s := fun s => by
      exact ((hQ (-s)).scomp s (hasDerivAt_neg s)).congr_deriv (by simp)
    have hL' : ∀ s, LipschitzOnWith K (-R) (ball (x (c - s)) δ) := fun s => by
      have := (hL (c - s))
      intro a ha b hb
      have h := this ha hb
      simpa [edist_neg_neg] using h
    have key := traj_close (x := fun s => x (c - s)) (Q := fun s => Q (-s)) hL' hx' hQ'
      (a := 0) (b := L) (by simpa using h0) (by simpa using hε) (-t) ⟨by linarith, by linarith [ht.1]⟩
    have e : c - -t = c + t := by ring
    simp only [neg_neg, e] at key
    refine key.trans ?_
    gcongr
    · linarith [ht.1]

/-- A `C²` map near a compact set: uniform Lipschitz bound and quadratic Taylor remainder. -/
lemma C2_near_compact [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {O : Set E} (hO : IsOpen O) (hf : ContDiffOn ℝ 2 f O)
    {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ δ > 0, ∃ D, 0 ≤ D ∧ ∀ p ∈ K, closedBall p δ ⊆ O ∧
      (∀ y ∈ closedBall p δ, ∀ y' ∈ closedBall p δ, ‖f y - f y'‖ ≤ D * ‖y - y'‖) ∧
      ∀ y ∈ closedBall p δ, ‖f y - f p - fderiv ℝ f p (y - p)‖ ≤ D * ‖y - p‖ ^ 2 := by
  have hf1 : ContDiffOn ℝ 1 f O := hf.of_le (by norm_num)
  have hdf : ContDiffOn ℝ 1 (fderiv ℝ f) O := hf.fderiv_of_isOpen hO (by norm_num)
  obtain ⟨δ₁, hδ₁, D₁, hD₁, h₁⟩ := FiniteEnergyPlane.exists_lipschitz_near_compact hO hf1 hK hKO
  obtain ⟨δ₂, hδ₂, D₂, hD₂, h₂⟩ := FiniteEnergyPlane.exists_lipschitz_near_compact hO hdf hK hKO
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max D₁ D₂, le_max_of_le_left hD₁, ?_⟩
  intro p hp
  have hb1 : closedBall p (min δ₁ δ₂) ⊆ closedBall p δ₁ := closedBall_subset_closedBall (min_le_left _ _)
  have hb2 : closedBall p (min δ₁ δ₂) ⊆ closedBall p δ₂ := closedBall_subset_closedBall (min_le_right _ _)
  obtain ⟨hO1, hL1⟩ := h₁ p hp
  obtain ⟨-, hL2⟩ := h₂ p hp
  refine ⟨hb1.trans hO1, ?_, ?_⟩
  · intro y hy y' hy'
    refine ((hL1 y (hb1 hy)).2 y' (hb1 hy')).trans ?_
    gcongr
    exact le_max_left _ _
  · intro y hy
    have hdiff : ∀ z ∈ O, DifferentiableAt ℝ f z := fun z hz =>
      (hf1.differentiableOn one_ne_zero z hz).differentiableAt (hO.mem_nhds hz)
    set s := closedBall p ‖y - p‖ with hs
    have hsb : s ⊆ closedBall p (min δ₁ δ₂) :=
      closedBall_subset_closedBall (by simpa [dist_eq_norm] using hy)
    have hp0 : p ∈ closedBall p (min δ₁ δ₂) := mem_closedBall_self (lt_min hδ₁ hδ₂).le
    have key := (convex_closedBall p ‖y - p‖).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (f := fun z => f z - fderiv ℝ f p z) (C := max D₁ D₂ * ‖y - p‖) (x := p) (y := y)
      (fun z hz => (hdiff z (hO1 (hb1 (hsb hz)))).sub (fderiv ℝ f p).differentiableAt)
      (fun z hz => by
        rw [fderiv_fun_sub (hdiff z (hO1 (hb1 (hsb hz)))) (fderiv ℝ f p).differentiableAt,
          ContinuousLinearMap.fderiv]
        have h3 := (hL2 z (hb2 (hsb hz))).2 p (hb2 hp0)
        have hz' : ‖z - p‖ ≤ ‖y - p‖ := by
          rw [hs, mem_closedBall, dist_eq_norm] at hz; exact hz
        calc ‖fderiv ℝ f z - fderiv ℝ f p‖ ≤ D₂ * ‖z - p‖ := h3
          _ ≤ max D₁ D₂ * ‖y - p‖ := mul_le_mul (le_max_right _ _) hz' (norm_nonneg _)
              (le_max_of_le_left hD₁))
      (mem_closedBall_self (norm_nonneg _)) (by simp [hs, dist_eq_norm])
    have e : f y - fderiv ℝ f p y - (f p - fderiv ℝ f p p) = f y - f p - fderiv ℝ f p (y - p) := by
      rw [map_sub]; abel
    rw [e] at key
    calc _ ≤ max D₁ D₂ * ‖y - p‖ * ‖y - p‖ := key
      _ = max D₁ D₂ * ‖y - p‖ ^ 2 := by ring

/-- A `C¹` map on `ℝ × ball`, periodic in the first variable, is uniformly Lipschitz in the
second variable on `ℝ × closedBall (r/2)`, for small increments. -/
lemma periodic_lipschitz_snd [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (Φ : ℝ × E → F) {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    (hΦ : ContDiffOn ℝ 1 Φ (univ ×ˢ ball (0 : E) r))
    (hper : ∀ (φ : ℝ) (u : E), Φ (φ + T, u) = Φ (φ, u)) :
    ∃ δ > 0, ∃ D, 0 ≤ D ∧ ∀ (φ : ℝ) (u u' : E), ‖u‖ ≤ r / 2 → ‖u' - u‖ ≤ δ →
      ‖Φ (φ, u') - Φ (φ, u)‖ ≤ D * ‖u' - u‖ := by
  have hO : IsOpen ((univ : Set ℝ) ×ˢ ball (0 : E) r) := isOpen_univ.prod isOpen_ball
  have hK : IsCompact (Icc (0 : ℝ) T ×ˢ closedBall (0 : E) (r / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKO : Icc (0 : ℝ) T ×ˢ closedBall (0 : E) (r / 2) ⊆ (univ : Set ℝ) ×ˢ ball (0 : E) r :=
    prod_mono (subset_univ _) (closedBall_subset_ball (by linarith))
  obtain ⟨δ, hδ, D, hD, h⟩ := FiniteEnergyPlane.exists_lipschitz_near_compact hO hΦ hK hKO
  refine ⟨δ, hδ, D, hD, ?_⟩
  intro φ u u' hu hu'
  have hp : Function.Periodic (fun φ => (Φ (φ, u), Φ (φ, u'))) T := fun φ => by
    simp only [hper]
  obtain ⟨φ', hφ', he⟩ := hp.exists_mem_Ico₀ hT φ
  simp only [Prod.mk.injEq] at he
  rw [he.1, he.2]
  have hpK : (φ', u) ∈ Icc (0 : ℝ) T ×ˢ closedBall (0 : E) (r / 2) :=
    ⟨Ico_subset_Icc_self hφ', by simpa using hu⟩
  obtain ⟨-, hL⟩ := h _ hpK
  have hm1 : (φ', u') ∈ closedBall (φ', u) δ := by
    rw [mem_closedBall, Prod.dist_eq]; simp [dist_eq_norm, hu', hδ.le]
  have hm2 : (φ', u) ∈ closedBall (φ', u) δ := mem_closedBall_self hδ.le
  have := (hL _ hm1).2 _ hm2
  have hn : ‖((φ', u') : ℝ × E) - (φ', u)‖ = ‖u' - u‖ := by
    rw [Prod.norm_def]; simp
  rwa [hn] at this

/-- A continuous periodic function is bounded. -/
lemma periodic_bdd {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {T : ℝ} (hT : 0 < T)
    (hf : Continuous f) (hper : Function.Periodic f T) : ∃ M, 0 ≤ M ∧ ∀ t, ‖f t‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun t => ?_⟩
  obtain ⟨t', ht', he⟩ := hper.exists_mem_Ico₀ hT t
  rw [he]
  exact (hM t' (Ico_subset_Icc_self ht')).trans (le_max_left _ _)

end TCBase

/-! A trajectory near a reference trajectory is quadratically close to the linearization. -/

namespace FiniteEnergyPlane

open Metric Set

theorem norm_sub_sub_linearized_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : E → E} {x y v : ℝ → E} {δ D L M c : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hlip : ∀ t, ∀ z ∈ closedBall (x t) δ, ∀ z' ∈ closedBall (x t) δ,
      ‖R z - R z'‖ ≤ D * ‖z - z'‖)
    (hquad : ∀ t, ∀ z ∈ closedBall (x t) δ,
      ‖R z - R (x t) - fderiv ℝ R (x t) (z - x t)‖ ≤ D * ‖z - x t‖ ^ 2)
    (hx : ∀ t, HasDerivAt x (R (x t)) t) (hy : ∀ t, HasDerivAt y (R (y t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (x (c + t)) (v t)) t)
    (hvM : ∀ t ∈ Icc (-L) L, ‖v t‖ ≤ M) (hMδ : M ≤ δ)
    (hy0 : ‖y 0 - x c‖ * Real.exp (D * L) < δ) :
    ∀ t ∈ Icc (-L) L, ‖y t - x (c + t)‖ ≤ ‖y 0 - x c‖ * Real.exp (D * L) ∧
      ‖y t - x (c + t) - v t‖ ≤
        (‖y 0 - x c - v 0‖ + D * M ^ 2 * L) * Real.exp ((D + 1) * L) := by
  set KR : NNReal := D.toNNReal with hKR
  have hKRe : (KR : ℝ) = D := Real.coe_toNNReal _ hD
  have hLipR : ∀ t, LipschitzOnWith KR R (ball (x t) δ) := fun t => by
    rw [hKR]
    refine LipschitzOnWith.of_dist_le' fun z hz z' hz' => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact hlip t z (ball_subset_closedBall hz) z' (ball_subset_closedBall hz')
  have hyx : ∀ t ∈ Icc (-L) L, ‖y t - x (c + t)‖ ≤ ‖y 0 - x c‖ * Real.exp (D * L) := by
    intro t ht
    have := TCBase.traj_close_two hLipR hx hy (c := c) (L := L) (ε := ‖y 0 - x c‖)
      (by rw [dist_eq_norm]) (by rw [hKRe]; exact hy0) t ht
    rwa [dist_eq_norm, hKRe] at this
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hvM 0 ⟨by linarith, hL⟩)
  have hed : ∀ t ∈ Icc (-L) L, HasDerivAt (fun t => y t - x (c + t) - v t)
      (R (y t) - R (x (c + t)) - fderiv ℝ R (x (c + t)) (v t)) t :=
    fun t _ => ((hy t).sub ((hx (c + t)).comp_const_add c t)).sub (hv t)
  have heb : ∀ t ∈ Icc (-L) L, ‖R (y t) - R (x (c + t)) - fderiv ℝ R (x (c + t)) (v t)‖ ≤
      (D + 1) * ‖(fun t => y t - x (c + t) - v t) t‖ + D * M ^ 2 := by
    intro t ht
    have hyB : y t ∈ closedBall (x (c + t)) δ := by
      rw [mem_closedBall, dist_eq_norm]; exact (hyx t ht).trans hy0.le
    have hvB : x (c + t) + v t ∈ closedBall (x (c + t)) δ := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact (hvM t ht).trans hMδ
    have h1 := hlip (c + t) (y t) hyB (x (c + t) + v t) hvB
    have h2 := hquad (c + t) _ hvB
    rw [add_sub_cancel_left] at h2
    have hsplit : R (y t) - R (x (c + t)) - fderiv ℝ R (x (c + t)) (v t) =
        (R (y t) - R (x (c + t) + v t)) + (R (x (c + t) + v t) -
          R (x (c + t)) - fderiv ℝ R (x (c + t)) (v t)) := by abel
    have hye : y t - (x (c + t) + v t) = y t - x (c + t) - v t := by abel
    rw [hye] at h1
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have hv2 : ‖v t‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hvM t ht) 2
    have h3 : D * ‖v t‖ ^ 2 ≤ D * M ^ 2 := mul_le_mul_of_nonneg_left hv2 hD
    have h4 : D * ‖y t - x (c + t) - v t‖ ≤ (D + 1) * ‖y t - x (c + t) - v t‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    simp only
    linarith
  intro t ht
  refine ⟨hyx t ht, ?_⟩
  have := TCBase.gronwall_two (by linarith : (0:ℝ) < D + 1) (by positivity) hL hed heb t ht
  simpa using this

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Set

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : E → E} {x y v : ℝ → E} {δ D L M c : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hlip : ∀ t, ∀ z ∈ closedBall (x t) δ, ∀ z' ∈ closedBall (x t) δ,
      ‖R z - R z'‖ ≤ D * ‖z - z'‖)
    (hquad : ∀ t, ∀ z ∈ closedBall (x t) δ,
      ‖R z - R (x t) - fderiv ℝ R (x t) (z - x t)‖ ≤ D * ‖z - x t‖ ^ 2)
    (hx : ∀ t, HasDerivAt x (R (x t)) t) (hy : ∀ t, HasDerivAt y (R (y t)) t)
    (hv : ∀ t, HasDerivAt v (fderiv ℝ R (x (c + t)) (v t)) t)
    (hvM : ∀ t ∈ Icc (-L) L, ‖v t‖ ≤ M) (hMδ : M ≤ δ)
    (hy0 : ‖y 0 - x c‖ * Real.exp (D * L) < δ) :
    ∀ t ∈ Icc (-L) L, ‖y t - x (c + t)‖ ≤ ‖y 0 - x c‖ * Real.exp (D * L) ∧
      ‖y t - x (c + t) - v t‖ ≤
        (‖y 0 - x c - v 0‖ + D * M ^ 2 * L) * Real.exp ((D + 1) * L) :=
  norm_sub_sub_linearized_le_aux hD hL hlip hquad hx hy hv hvM hMδ hy0
