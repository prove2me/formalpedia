-- Prove2me | solution 1 for CauchyRiemannIndex.linearODE_continuous_param
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T12:24:35.542046+00:00
-- url     : https://prove2.me/submissions/9d040d83-b2f2-488c-99a4-832594b8a6a9

import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Algebra.Module.Basic

open Filter Topology Set Metric
open scoped NNReal

namespace CauchyRiemannIndex

/-- Uniform closeness of the solutions on `[0, 1]` for parameters near `τ₀`. -/
lemma crj_ode_unif {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B : X × ℝ → E →L[ℝ] E) (hB : Continuous B) (x₀ : X → E)
    (hx₀ : Continuous x₀) (x : X → ℝ → E) (hx0 : ∀ τ, x τ 0 = x₀ τ)
    (hx : ∀ τ t, HasDerivAt (x τ) (B (τ, t) (x τ t)) t) (τ₀ : X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ τ in 𝓝 τ₀, ∀ t ∈ Icc (0 : ℝ) 1, dist (x τ t) (x τ₀ t) < ε := by
  have hxc : ∀ τ, Continuous (x τ) := fun τ =>
    continuous_iff_continuousAt.2 fun t => (hx τ t).continuousAt
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hxc τ₀).continuousOn
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun t => B (τ₀, t)) (hB.comp (continuous_const.prodMk continuous_id)).continuousOn
  set K : ℝ≥0 := ⟨max K₀ 0 + 1, by positivity⟩ with hKdef
  have hKval : (K : ℝ) = max K₀ 0 + 1 := rfl
  have hKpos : (0 : ℝ) < K := by rw [hKval]; positivity
  set c := Real.exp (K : ℝ) with hcdef
  have hc : 0 < c := Real.exp_pos _
  set M' := max M 0 + 1 with hM'def
  have hM' : 0 < M' := by positivity
  set δ := ε / (4 * c) with hδdef
  set η := min 1 (ε * K / (4 * c * M')) with hηdef
  have hδ : 0 < δ := by positivity
  have hη : 0 < η := lt_min one_pos (by positivity)
  have htube : ∀ᶠ τ in 𝓝 τ₀, ∀ t ∈ Icc (0 : ℝ) 1, dist (B (τ, t)) (B (τ₀, t)) < η := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro y _
    have hf : Continuous fun z : X × ℝ => dist (B z) (B (τ₀, z.2)) :=
      hB.dist (hB.comp (continuous_const.prodMk continuous_snd))
    exact hf.continuousAt.eventually_lt continuousAt_const (by simpa using hη)
  have hinit : ∀ᶠ τ in 𝓝 τ₀, x₀ τ ∈ ball (x₀ τ₀) δ :=
    hx₀.continuousAt.eventually (ball_mem_nhds _ hδ)
  filter_upwards [htube, hinit] with τ hτ hτ0
  intro t ht
  have hlip : ∀ s ∈ Ico (0 : ℝ) 1, LipschitzOnWith K (fun y => B (τ, s) y) univ := by
    intro s hs
    refine (LipschitzWith.weaken (B (τ, s)).lipschitz ?_).lipschitzOnWith
    have h1 : ‖B (τ, s) - B (τ₀, s)‖ < η := by
      rw [← dist_eq_norm]; exact hτ s (Ico_subset_Icc_self hs)
    have h2 := hK₀ s (Ico_subset_Icc_self hs)
    have h3 : ‖B (τ, s)‖ ≤ K := by
      rw [hKval]
      calc ‖B (τ, s)‖ = ‖(B (τ, s) - B (τ₀, s)) + B (τ₀, s)‖ := by rw [sub_add_cancel]
        _ ≤ ‖B (τ, s) - B (τ₀, s)‖ + ‖B (τ₀, s)‖ := norm_add_le _ _
        _ ≤ 1 + max K₀ 0 := add_le_add (h1.le.trans (min_le_left _ _)) (h2.trans (le_max_left _ _))
        _ = max K₀ 0 + 1 := add_comm _ _
    exact_mod_cast h3
  have hg : ∀ s ∈ Ico (0 : ℝ) 1,
      dist (B (τ₀, s) (x τ₀ s)) (B (τ, s) (x τ₀ s)) ≤ η * M' := by
    intro s hs
    rw [dist_eq_norm, ← ContinuousLinearMap.sub_apply]
    calc ‖(B (τ₀, s) - B (τ, s)) (x τ₀ s)‖ ≤ ‖B (τ₀, s) - B (τ, s)‖ * ‖x τ₀ s‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ η * M' := by
          apply mul_le_mul _ _ (norm_nonneg _) hη.le
          · rw [← dist_eq_norm, dist_comm]; exact (hτ s (Ico_subset_Icc_self hs)).le
          · have := hM s (Ico_subset_Icc_self hs)
            have := le_max_left M 0
            rw [hM'def]; linarith
  have ha : dist (x τ 0) (x τ₀ 0) ≤ δ := by
    rw [hx0, hx0]; exact (mem_ball.1 hτ0).le
  have key := dist_le_of_approx_trajectories_ODE_of_mem (v := fun s y => B (τ, s) y)
    (s := fun _ => univ) (K := K) (f := x τ) (g := x τ₀)
    (f' := fun s => B (τ, s) (x τ s)) (g' := fun s => B (τ₀, s) (x τ₀ s))
    (a := 0) (b := 1) (εf := 0) (εg := η * M') (δ := δ)
    hlip (hxc τ).continuousOn (fun s _ => (hx τ s).hasDerivWithinAt) (by intro s _; simp)
    (fun _ _ => trivial) (hxc τ₀).continuousOn (fun s _ => (hx τ₀ s).hasDerivWithinAt) hg
    (fun _ _ => trivial) ha t ht
  rw [gronwallBound_of_K_ne_0 hKpos.ne', sub_zero, zero_add] at key
  have he : Real.exp ((K : ℝ) * t) ≤ c :=
    Real.exp_le_exp.2 (mul_le_of_le_one_right hKpos.le ht.2)
  have he1 : 0 ≤ Real.exp ((K : ℝ) * t) - 1 := by
    have := Real.add_one_le_exp ((K : ℝ) * t)
    nlinarith [mul_nonneg hKpos.le ht.1]
  have b1 : δ * Real.exp ((K : ℝ) * t) ≤ ε / 4 := by
    calc δ * Real.exp ((K : ℝ) * t) ≤ δ * c := mul_le_mul_of_nonneg_left he hδ.le
      _ = ε / 4 := by rw [hδdef]; field_simp
  have b2 : η * M' / K * (Real.exp ((K : ℝ) * t) - 1) ≤ ε / 4 := by
    calc η * M' / K * (Real.exp ((K : ℝ) * t) - 1) ≤ η * M' / K * c :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = η * (M' * c / K) := by ring
      _ ≤ (ε * K / (4 * c * M')) * (M' * c / K) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = ε / 4 := by field_simp
  linarith

theorem crj_ode_param {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B : X × ℝ → E →L[ℝ] E) (hB : Continuous B) (x₀ : X → E)
    (hx₀ : Continuous x₀) (x : X → ℝ → E) (hx0 : ∀ τ, x τ 0 = x₀ τ)
    (hx : ∀ τ t, HasDerivAt (x τ) (B (τ, t) (x τ t)) t) :
    Continuous (fun p : X × unitInterval => x p.1 p.2) := by
  have hxc : ∀ τ, Continuous (x τ) := fun τ =>
    continuous_iff_continuousAt.2 fun t => (hx τ t).continuousAt
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨τ₀, t₀⟩ := p₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have h1 := crj_ode_unif B hB x₀ hx₀ x hx0 hx τ₀ (half_pos hε)
  have h2 : ∀ᶠ t : unitInterval in 𝓝 t₀, x τ₀ t ∈ ball (x τ₀ t₀) (ε / 2) :=
    ((hxc τ₀).comp continuous_subtype_val).continuousAt.eventually
      (ball_mem_nhds _ (half_pos hε))
  rw [nhds_prod_eq]
  filter_upwards [h1.prod_mk h2] with p hp
  calc dist (x p.1 p.2) (x τ₀ t₀) ≤ dist (x p.1 p.2) (x τ₀ p.2) + dist (x τ₀ p.2) (x τ₀ t₀) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hp.1 p.2 p.2.2) (mem_ball.1 hp.2)
    _ = ε := add_halves ε

end CauchyRiemannIndex

theorem solution {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (B : X × ℝ → E →L[ℝ] E) (hB : Continuous B) (x₀ : X → E)
    (hx₀ : Continuous x₀) (x : X → ℝ → E) (hx0 : ∀ τ, x τ 0 = x₀ τ)
    (hx : ∀ τ t, HasDerivAt (x τ) (B (τ, t) (x τ t)) t) :
    Continuous (fun p : X × unitInterval => x p.1 p.2) :=
  CauchyRiemannIndex.crj_ode_param B hB x₀ hx₀ x hx0 hx
