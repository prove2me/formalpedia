-- Prove2me | solution 1 for FiniteEnergyPlane.hasDerivAt_unitaryFrame_apply_of_linearized
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T15:54:53.121167+00:00
-- url     : https://prove2.me/submissions/9ae29b90-e425-4b4e-8761-c24e8ecbcc4f

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitz_near_compact
import Definitions.Def_FiniteEnergyPlane_OpenBook
import Theorems.Thm_AsymptoticOperator_linearODE_existsUnique
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_FiniteEnergyPlane_linReebFlow_spec
import Theorems.Thm_FiniteEnergyPlane_linReebFlow_unitaryFrame_eq

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

/-! The linearized equation `ζ' = J₀ S ζ` for `exists_tubeCoords_near_linearized`. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

noncomputable section

/-- The operator `J₀ S(t)` as a continuous linear map. -/
def tcB (S : ℝ → CauchyRiemannIndex.Mat 1) (t : ℝ) :
    CauchyRiemannIndex.Vec 1 →L[ℝ] CauchyRiemannIndex.Vec 1 :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t))

theorem tcB_apply (S : ℝ → CauchyRiemannIndex.Mat 1) (t : ℝ) (v : CauchyRiemannIndex.Vec 1) :
    tcB S t v = Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) v := rfl

theorem tcB_continuous (S : ℝ → CauchyRiemannIndex.Mat 1) (hS : Continuous S) :
    Continuous (tcB S) := by
  let Φl : CauchyRiemannIndex.Mat 1 →ₗ[ℝ]
      (CauchyRiemannIndex.Vec 1 →L[ℝ] CauchyRiemannIndex.Vec 1) :=
    { toFun := fun N => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin N)
      map_add' := fun N N' => by ext x : 1; simp
      map_smul' := fun c N => by ext x : 1; simp }
  have hM : Continuous fun t => CauchyRiemannIndex.J₀ 1 * S t :=
    continuous_const.matrix_mul hS
  exact (LinearMap.continuous_of_finiteDimensional Φl).comp hM

theorem tc_sol_unique (S : ℝ → CauchyRiemannIndex.Mat 1) (hS : Continuous S)
    {ζ ζ' : ℝ → CauchyRiemannIndex.Vec 1}
    (hζ : ∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ t)) t)
    (hζ' : ∀ t, HasDerivAt ζ' (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ' t)) t)
    (h0 : ζ 0 = ζ' 0) : ζ = ζ' := by
  obtain ⟨x, -, hx⟩ := AsymptoticOperator.linearODE_existsUnique (tcB S) (tcB_continuous S hS) (ζ 0)
  have e1 := hx ζ ⟨rfl, hζ⟩
  have e2 := hx ζ' ⟨h0.symm, hζ'⟩
  rw [e1, e2]

theorem tc_fund_apply_hasDerivAt (S : ℝ → CauchyRiemannIndex.Mat 1)
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1) (hΨ : CauchyRiemannIndex.IsFundamentalSolution S Ψ)
    (w : CauchyRiemannIndex.Vec 1) (t : ℝ) :
    HasDerivAt (fun t => Matrix.toEuclideanLin (Ψ t) w)
      (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t)
        (Matrix.toEuclideanLin (Ψ t) w)) t := by
  let _ : NormedAddCommGroup (CauchyRiemannIndex.Mat 1) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (CauchyRiemannIndex.Mat 1) := Matrix.normedSpace
  let Lw : CauchyRiemannIndex.Mat 1 →ₗ[ℝ] CauchyRiemannIndex.Vec 1 :=
    { toFun := fun N => Matrix.toEuclideanLin N w
      map_add' := fun N N' => by simp
      map_smul' := fun c N => by simp }
  have h := (LinearMap.toContinuousLinearMap Lw).hasFDerivAt.comp_hasDerivAt t (hΨ.2 t)
  refine h.congr_deriv ?_
  show Matrix.toEuclideanLin _ w = _
  rw [Matrix.toLpLin_mul, LinearMap.comp_apply]

/-- A solution of `ζ' = J₀ S ζ` through `a₀` at time `t₀`. -/
theorem tc_sol_exists (S : ℝ → CauchyRiemannIndex.Mat 1) (hS : Continuous S) (t₀ : ℝ)
    (a₀ : CauchyRiemannIndex.Vec 1) :
    ∃ ζ : ℝ → CauchyRiemannIndex.Vec 1,
      (∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ t)) t) ∧
      ζ t₀ = a₀ := by
  have hc : Continuous fun t => tcB S (t + t₀) :=
    (tcB_continuous S hS).comp (continuous_id.add continuous_const)
  obtain ⟨z, ⟨hz0, hz⟩, -⟩ := AsymptoticOperator.linearODE_existsUnique _ hc a₀
  refine ⟨fun t => z (t - t₀), fun t => ?_, by simp [hz0]⟩
  have := (hz (t - t₀)).comp_sub_const t t₀
  simpa [tcB_apply, sub_add_cancel] using this

/-- Two-sided growth bound for solutions of `ζ' = J₀ S ζ` over a window of length `Λ`. -/
theorem tc_sol_bound (S : ℝ → CauchyRiemannIndex.Mat 1) (hS : Continuous S)
    (hper : Function.Periodic S 1) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1,
      (∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ t)) t) →
      ∀ t₀ s : ℝ, |s| ≤ Λ → ‖ζ (t₀ + s)‖ ≤ C * ‖ζ t₀‖ ∧ ‖ζ t₀‖ ≤ C * ‖ζ (t₀ + s)‖ := by
  obtain ⟨M, hM0, hM⟩ := TCBase.periodic_bdd one_pos (tcB_continuous S hS)
    (fun t => by simp only [tcB, hper t])
  have hK : 0 < M + 1 := by linarith
  refine ⟨Real.exp ((M + 1) * Λ), Real.one_le_exp (by positivity), ?_⟩
  intro ζ hζ
  have key : ∀ t₁ s : ℝ, |s| ≤ Λ → ‖ζ (t₁ + s)‖ ≤ Real.exp ((M + 1) * Λ) * ‖ζ t₁‖ := by
    intro t₁ s hs
    have hd : ∀ u ∈ Icc (-Λ) Λ, HasDerivAt (fun u => ζ (t₁ + u))
        (tcB S (t₁ + u) (ζ (t₁ + u))) u := fun u _ => by
      have := (hζ (t₁ + u)).comp_const_add t₁ u
      simpa [tcB_apply] using this
    have hb : ∀ u ∈ Icc (-Λ) Λ, ‖tcB S (t₁ + u) (ζ (t₁ + u))‖ ≤
        (M + 1) * ‖(fun u => ζ (t₁ + u)) u‖ + 0 := fun u _ => by
      have h1 := (tcB S (t₁ + u)).le_opNorm (ζ (t₁ + u))
      have h2 := hM (t₁ + u)
      simp only [add_zero]
      nlinarith [norm_nonneg (ζ (t₁ + u))]
    have := TCBase.gronwall_two hK le_rfl hΛ hd hb s ⟨by linarith [neg_abs_le s], by
      linarith [le_abs_self s]⟩
    simpa [mul_comm] using this
  intro t₀ s hs
  refine ⟨key t₀ s hs, ?_⟩
  have := key (t₀ + s) (-s) (by rwa [abs_neg])
  simpa using this

end

end FiniteEnergyPlane

/-! Children for `exists_tubeCoords_near_linearized`: solutions of `ζ' = J₀ S ζ` and their
transport by a unitary frame. -/

namespace FiniteEnergyPlane

open Set
open scoped ContDiff

theorem exists_solution_norm_le_of_isSymLoop_aux (S : ℝ → CauchyRiemannIndex.Mat 1)
    (hS : CauchyRiemannIndex.IsSymLoop S) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ (t₀ : ℝ) (a₀ : CauchyRiemannIndex.Vec 1), ∃ ζ : ℝ → CauchyRiemannIndex.Vec 1,
        (∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ t)) t) ∧
        ζ t₀ = a₀) ∧
      ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1,
        (∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ t)) t) →
        ∀ t₀ s : ℝ, |s| ≤ Λ → ‖ζ (t₀ + s)‖ ≤ C * ‖ζ t₀‖ ∧ ‖ζ t₀‖ ≤ C * ‖ζ (t₀ + s)‖ := by
  obtain ⟨C, hC, hb⟩ := tc_sol_bound S hS.1 hS.2.1 Λ hΛ
  exact ⟨C, hC, fun t₀ a₀ => tc_sol_exists S hS.1 t₀ a₀, hb⟩

theorem hasDerivAt_unitaryFrame_apply_of_linearized_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (ζ : ℝ → CauchyRiemannIndex.Vec 1)
    (hζ : ∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * Sinf t) (ζ t)) t)
    (τ : ℝ) :
    HasDerivAt (fun τ => Z (τ / P.T) (ζ (τ / P.T)))
      (fderiv ℝ (reeb H) (P.x τ) (Z (τ / P.T) (ζ (τ / P.T)))) τ := by
  have hT : 0 < P.T := P.T_pos
  obtain ⟨Φ, hΦ⟩ := (linReebFlow_spec H hH P).1.exists
  obtain ⟨Ψ, hΨ, -⟩ := CauchyRiemannIndex.fundamentalSolution_existsUnique 1 Sinf hSym.1
  have hζΨ : ζ = fun t => Matrix.toEuclideanLin (Ψ t) (ζ 0) :=
    tc_sol_unique Sinf hSym.1 hζ (tc_fund_apply_hasDerivAt Sinf Ψ hΨ (ζ 0)) (by simp [hΨ.1])
  have hfr := linReebFlow_unitaryFrame_eq H hH J P Z hZ Sinf hA Ψ hΨ Φ hΦ
  have hvΦ : ∀ τ, Z (τ / P.T) (ζ (τ / P.T)) = Φ τ (Z 0 (ζ 0)) := fun τ => by
    have := hfr (τ / P.T) (ζ 0)
    rw [mul_div_cancel₀ _ hT.ne'] at this
    rw [this]
    conv_lhs => rw [hζΨ]
  have hfun : (fun τ => Z (τ / P.T) (ζ (τ / P.T))) = fun τ => Φ τ (Z 0 (ζ 0)) := funext hvΦ
  rw [hfun, hvΦ τ]
  have h1 := (ContinuousLinearMap.apply ℝ (V 1) (Z 0 (ζ 0))).hasFDerivAt.comp_hasDerivAt
    τ (hΦ.2 τ)
  exact h1.congr_deriv (by simp)

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (ζ : ℝ → CauchyRiemannIndex.Vec 1)
    (hζ : ∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * Sinf t) (ζ t)) t)
    (τ : ℝ) :
    HasDerivAt (fun τ => Z (τ / P.T) (ζ (τ / P.T)))
      (fderiv ℝ (reeb H) (P.x τ) (Z (τ / P.T) (ζ (τ / P.T)))) τ :=
  hasDerivAt_unitaryFrame_apply_of_linearized_aux H hH J P Z hZ Sinf hSym hA ζ hζ τ
