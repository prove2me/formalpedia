-- Prove2me | solution 1 for DatkoDelayWave.BoundaryDelay.theorem_iii_destabilization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:24:00.971397+00:00
-- url     : https://prove2.me/submissions/0f5903da-127c-4c8b-ac51-1ab35a242fc4

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

-- carved verbatim out of submission 9e78ff97-3a87-4a96-9f66-6a86542faea0, lines 795-855

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
open Set Filter Metric Complex
open scoped Topology

theorem exists_zero_of_norm_lt_on_sphere (F : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hF : DiffContOnCl ℂ F (Metric.ball c r))
    (hlt : ∀ z ∈ Metric.sphere c r, ‖F c‖ < ‖F z‖) :
    ∃ z ∈ Metric.ball c r, F z = 0 := by
  have h2 : ContinuousOn (fun z => ‖F z‖) (closedBall c r) :=
    continuous_norm.comp_continuousOn (closure_ball c hr.ne.symm ▸ hF.continuousOn)
  obtain ⟨z, hz1, hz2⟩ : ∃ z ∈ ball c r, IsLocalMin (fun z => ‖F z‖) z :=
    exists_isLocalMin_mem_ball h2 (mem_closedBall_self hr.le) fun z hz => hlt z hz
  refine ⟨z, hz1, ?_⟩
  have h6 := hF.differentiableOn.eventually_differentiableAt (isOpen_ball.mem_nhds hz1)
  refine (eventually_eq_or_eq_zero_of_isLocalMin_norm h6 hz2).resolve_left fun key => ?_
  have h3 : AnalyticOnNhd ℂ F (ball c r) := hF.differentiableOn.analyticOnNhd isOpen_ball
  have h7 : ∀ᶠ w in 𝓝 z, F w = F z := by filter_upwards [key] with h; simp
  replace h7 : ∃ᶠ w in 𝓝[≠] z, F w = F z := (h7.filter_mono nhdsWithin_le_nhds).frequently
  have h8 : IsPreconnected (ball c r) := (convex_ball c r).isPreconnected
  have h9 := h3.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const h8 hz1 h7
  have hcont : ContinuousOn F (closedBall c r) := by
    have := hF.continuousOn; rwa [closure_ball c hr.ne.symm] at this
  have hcl : EqOn F (fun _ => F z) (closedBall c r) :=
    h9.of_subset_closure hcont continuousOn_const ball_subset_closedBall
      (by rw [closure_ball c hr.ne.symm])
  have hw : ∃ w, w ∈ sphere c r := NormedSpace.sphere_nonempty.mpr hr.le
  obtain ⟨w, hw⟩ := hw
  have e1 : F w = F z := hcl (sphere_subset_closedBall hw)
  have e2 : F c = F z := hcl (mem_closedBall_self hr.le)
  have := hlt w hw
  rw [e1, e2] at this
  exact absurd this (lt_irrefl _)

theorem iso_sphere (g : ℂ → ℂ) (hg : Differentiable ℂ g) (ω₀ : ℂ) (hnt : ∃ ω, g ω ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ ∃ μ : ℝ, 0 < μ ∧ ∀ z ∈ sphere ω₀ ρ, μ ≤ ‖g z‖ := by
  have hAn : AnalyticOnNhd ℂ g univ := hg.differentiableOn.analyticOnNhd isOpen_univ
  have hnez : ∀ᶠ z in 𝓝[≠] ω₀, g z ≠ 0 := by
    rcases (hAn ω₀ (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      obtain ⟨w, hw⟩ := hnt
      have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ ω₀) h
      exact hw (this (mem_univ w))
    · exact h
  obtain ⟨ρ0, hρ0, hρ0'⟩ := Metric.mem_nhdsWithin_iff.mp hnez
  set ρ : ℝ := min (ρ0 / 2) (r / 2) with hρ
  have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρr : ρ < r := by have := min_le_right (ρ0 / 2) (r / 2); linarith
  have hρρ0 : ρ < ρ0 := by have := min_le_left (ρ0 / 2) (r / 2); linarith
  have hne : ∀ z ∈ sphere ω₀ ρ, g z ≠ 0 := by
    intro z hz
    have hzne : z ≠ ω₀ := ne_of_mem_sphere hz hρpos.ne.symm
    have : z ∈ ball ω₀ ρ0 ∩ {ω₀}ᶜ := ⟨by
      rw [mem_ball, mem_sphere.mp hz]; exact hρρ0, hzne⟩
    exact hρ0' this
  have hsne : (sphere ω₀ ρ).Nonempty := NormedSpace.sphere_nonempty.mpr hρpos.le
  have hcs : ContinuousOn (fun z => ‖g z‖) (sphere ω₀ ρ) :=
    (continuous_norm.comp hg.continuous).continuousOn
  obtain ⟨z1, hz1, hmin⟩ := (isCompact_sphere ω₀ ρ).exists_isMinOn hsne hcs
  refine ⟨ρ, hρpos, hρr, ‖g z1‖, ?_, fun z hz => hmin hz⟩
  rw [norm_pos_iff]; exact hne z1 hz1

theorem zero_persists (F : ℝ → ℂ → ℂ) (hcont : Continuous (fun p : ℝ × ℂ => F p.1 p.2))
    (hdiff : ∀ ε, Differentiable ℂ (F ε)) (ε₀ : ℝ) (ω₀ : ℂ) (h0 : F ε₀ ω₀ = 0)
    (hnt : ∃ ω, F ε₀ ω ≠ 0) (r : ℝ) (hr : 0 < r) :
    ∃ η > (0 : ℝ), ∀ ε, |ε - ε₀| < η → ∃ ω ∈ Metric.ball ω₀ r, F ε ω = 0 := by
  -- isolated zero
  have hAn : AnalyticOnNhd ℂ (F ε₀) univ := (hdiff ε₀).differentiableOn.analyticOnNhd isOpen_univ
  have hnez : ∀ᶠ z in 𝓝[≠] ω₀, F ε₀ z ≠ 0 := by
    rcases (hAn ω₀ (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      obtain ⟨w, hw⟩ := hnt
      have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ ω₀) h
      exact hw (this (mem_univ w))
    · exact h
  obtain ⟨ρ0, hρ0, hρ0'⟩ := Metric.mem_nhdsWithin_iff.mp hnez
  set ρ : ℝ := min (ρ0 / 2) (r / 2) with hρ
  have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρr : ρ < r := by have := min_le_right (ρ0 / 2) (r / 2); linarith
  have hρρ0 : ρ < ρ0 := by have := min_le_left (ρ0 / 2) (r / 2); linarith
  have hne : ∀ z ∈ closedBall ω₀ ρ, z ≠ ω₀ → F ε₀ z ≠ 0 := by
    intro z hz hzne
    have : z ∈ ball ω₀ ρ0 ∩ {ω₀}ᶜ := ⟨by
      rw [mem_ball]; exact lt_of_le_of_lt (mem_closedBall.mp hz) hρρ0, hzne⟩
    exact hρ0' this
  have hsne : (sphere ω₀ ρ).Nonempty := NormedSpace.sphere_nonempty.mpr hρpos.le
  have hcs : ContinuousOn (fun z => ‖F ε₀ z‖) (sphere ω₀ ρ) :=
    (continuous_norm.comp (hdiff ε₀).continuous).continuousOn
  obtain ⟨z1, hz1, hmin⟩ := (isCompact_sphere ω₀ ρ).exists_isMinOn hsne hcs
  set μ : ℝ := ‖F ε₀ z1‖ with hμ
  have hμpos : 0 < μ := by
    rw [hμ, norm_pos_iff]
    exact hne z1 (sphere_subset_closedBall hz1) (ne_of_mem_sphere hz1 hρpos.ne.symm)
  -- tube lemma
  have hev : ∀ᶠ ε in 𝓝 ε₀, ∀ z ∈ closedBall ω₀ ρ, ‖F ε z - F ε₀ z‖ < μ / 2 := by
    apply (isCompact_closedBall ω₀ ρ).eventually_forall_of_forall_eventually
    intro z _
    have hc : Continuous (fun p : ℝ × ℂ => ‖F p.1 p.2 - F ε₀ p.2‖) := by
      have : Continuous (fun p : ℝ × ℂ => F ε₀ p.2) := (hdiff ε₀).continuous.comp continuous_snd
      exact (hcont.sub this).norm
    have := hc.continuousAt (x := (ε₀, z))
    have h2 : ‖F ε₀ z - F ε₀ z‖ < μ / 2 := by simp; linarith
    exact this.eventually (gt_mem_nhds h2)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun ε hε => ?_⟩
  have hεd := hδ' (by rw [Real.dist_eq]; exact hε)
  obtain ⟨z, hz, hz0⟩ := exists_zero_of_norm_lt_on_sphere (F ε) ω₀ ρ hρpos
    (Differentiable.diffContOnCl (hdiff ε)) (by
      intro w hw
      have h1 := hεd w (sphere_subset_closedBall hw)
      have h2 := hεd ω₀ (mem_closedBall_self hρpos.le)
      have h3 : μ ≤ ‖F ε₀ w‖ := hmin hw
      rw [h0] at h2
      have h4 : ‖F ε ω₀‖ < μ / 2 := by simpa [h0] using (by simpa using h2 : ‖F ε ω₀ - 0‖ < μ / 2)
      have h5 := norm_sub_norm_le (F ε₀ w) (F ε w)
      rw [norm_sub_rev] at h5
      linarith)
  exact ⟨z, ball_subset_ball hρr.le hz, hz0⟩

end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
open Complex
open DatkoDelayWave
open DatkoDelayWave.BoundaryDelay
open Set Filter Metric
open scoped Topology

theorem K_pos (a : ℝ) : 0 < K a := Real.exp_pos _

theorem K_le_one (a : ℝ) (ha : 0 ≤ a) : K a ≤ 1 := by
  unfold K; rw [Real.exp_le_one_iff]; linarith

theorem f_h_regular (a k : ℝ) (ha : 0 ≤ a) (hk : 0 ≤ k) :
    Continuous (fun p : ℝ × ℂ => f a k p.1 p.2) ∧ Continuous (fun p : ℝ × ℂ => h a k p.1 p.2) ∧
    (∀ ε, Differentiable ℂ (f a k ε)) ∧ (∀ ε, Differentiable ℂ (h a k ε)) ∧
    ∀ ε, ∀ x : ℝ, 0 < x → f a k ε (x : ℂ) ≠ 0 ∧ h a k ε (x : ℂ) ≠ 0 := by
  have hf : Continuous (fun p : ℝ × ℂ => f a k p.1 p.2) := by
    unfold f; fun_prop
  have hdf : ∀ ε, Differentiable ℂ (f a k ε) := by
    intro ε; unfold f; fun_prop
  refine ⟨hf, ?_, hdf, ?_, ?_⟩
  · unfold h; refine Continuous.add ?_ ?_
    · exact continuous_snd.mul hf
    · fun_prop
  · intro ε; unfold h; exact ((differentiable_id).mul (hdf ε)).add (by fun_prop)
  · intro ε x hx
    have hK := K_pos a
    have hex : Real.exp (-2 * a) * Real.exp (-2 * x) < 1 := by
      rw [← Real.exp_add, Real.exp_lt_one_iff]; linarith
    have e1 : 0 < 1 + K a * Real.exp (-2 * x) := by positivity
    have e2 : 0 < 1 - K a * Real.exp (-2 * x) := by unfold K; linarith
    have hfeq : f a k ε (x : ℂ) = ((1 + K a * Real.exp (-2 * x)
        + k * Real.exp (-ε * x) * (1 - K a * Real.exp (-2 * x)) : ℝ) : ℂ) := by
      unfold f; push_cast
      simp [Complex.ofReal_exp]
    have fpos : 0 < 1 + K a * Real.exp (-2 * x)
        + k * Real.exp (-ε * x) * (1 - K a * Real.exp (-2 * x)) := by
      have : 0 ≤ k * Real.exp (-ε * x) * (1 - K a * Real.exp (-2 * x)) := by positivity
      linarith
    have hheq : h a k ε (x : ℂ) = (((x : ℝ) * (1 + K a * Real.exp (-2 * x)
        + k * Real.exp (-ε * x) * (1 - K a * Real.exp (-2 * x))) + a * (1 + K a * Real.exp (-2 * x)) : ℝ) : ℂ) := by
      unfold h; rw [hfeq]; push_cast
      simp [Complex.ofReal_exp]
    refine ⟨?_, ?_⟩
    · rw [hfeq]; exact_mod_cast fpos.ne'
    · rw [hheq]
      have : 0 < x * (1 + K a * Real.exp (-2 * x)
        + k * Real.exp (-ε * x) * (1 - K a * Real.exp (-2 * x))) + a * (1 + K a * Real.exp (-2 * x)) := by
        have := mul_pos hx fpos
        have : 0 ≤ a * (1 + K a * Real.exp (-2 * x)) := by positivity
        linarith
      exact_mod_cast this.ne'

theorem f_periodic_rational_delay (a k : ℝ) (m n : ℕ) (ω : ℂ) :
    f a k (2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1))
        (ω + ((2 * (n : ℝ) + 1) * Real.pi : ℝ) * I) =
      f a k (2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1)) ω := by
  have h1 : Complex.exp (-2 * (ω + ((2 * (n : ℝ) + 1) * Real.pi : ℝ) * I)) = Complex.exp (-2 * ω) := by
    have : -2 * (ω + ((2 * (n : ℝ) + 1) * Real.pi : ℝ) * I)
        = -2 * ω + ((-(2 * (n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have h2 : Complex.exp (-((2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) : ℝ) : ℂ)
      * (ω + ((2 * (n : ℝ) + 1) * Real.pi : ℝ) * I))
      = Complex.exp (-((2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) : ℝ) : ℂ) * ω) := by
    have hn : (2 * (n : ℂ) + 1) ≠ 0 := by
      have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      exact_mod_cast this
    have : -((2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) : ℝ) : ℂ)
        * (ω + ((2 * (n : ℝ) + 1) * Real.pi : ℝ) * I)
        = -((2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) : ℝ) : ℂ) * ω
          + ((-(2 * (m : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast; field_simp; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  unfold f
  rw [h1, h2]

theorem f_periodic_iter (a k ε p : ℝ)
    (hper : ∀ ω, f a k ε (ω + (p : ℂ) * I) = f a k ε ω) (j : ℕ) (ω : ℂ) :
    f a k ε (ω + ((j : ℝ) * p : ℝ) * I) = f a k ε ω := by
  induction j generalizing ω with
  | zero => simp
  | succ n ih =>
    have : ω + ((((n + 1 : ℕ) : ℝ) * p : ℝ) : ℂ) * I
        = (ω + (p : ℂ) * I) + (((n : ℝ) * p : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, ih, hper]

theorem h_zero_near_f_zero_translates (a k ε : ℝ) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (ω₀ : ℂ) (hf0 : f a k ε ω₀ = 0) (p : ℝ) (hp : 0 < p)
    (hper : ∀ ω, f a k ε (ω + (p : ℂ) * I) = f a k ε ω) (r : ℝ) (hr : 0 < r) (N : ℕ) :
    ∃ j : ℕ, N ≤ j ∧ ∃ ω : ℂ, ‖ω - (ω₀ + ((j : ℝ) * p : ℝ) * I)‖ < r ∧ h a k ε ω = 0 := by
  obtain ⟨_, _, hdf, _, hpos⟩ := f_h_regular a k ha hk
  obtain ⟨ρ, hρ, hρr, μ, hμ, hsph⟩ := iso_sphere (f a k ε) (hdf ε) ω₀
    ⟨((1 : ℝ) : ℂ), (hpos ε 1 one_pos).1⟩ r hr
  have hK1 := K_le_one a ha
  have hK0 := K_pos a
  set T : ℝ := ‖ω₀‖ + ρ with hT
  set B : ℝ := a * (1 + Real.exp (2 * T)) with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨J, hJ⟩ := exists_nat_gt ((T + 2 * B / μ + 1) / p)
  set j : ℕ := N + J with hj
  have hNj : N ≤ j := Nat.le_add_right _ _
  have hjp : T + 2 * B / μ + 1 < (j : ℝ) * p := by
    have h1 : T + 2 * B / μ + 1 < (J : ℝ) * p := by
      rw [div_lt_iff₀ hp] at hJ; exact hJ
    have h2 : (J : ℝ) ≤ j := by rw [hj]; push_cast; linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
    nlinarith
  set P : ℝ := (j : ℝ) * p with hP
  have hT0 : 0 ≤ T := by positivity
  have h2Bμ : 0 ≤ 2 * B / μ := by positivity
  -- the point
  let w : ℂ → ℂ := fun z => ω₀ + z + (P : ℂ) * I
  let S : ℂ → ℂ := fun z => (a : ℂ) * (1 + (K a : ℂ) * Complex.exp (-2 * w z)) / w z
  let G : ℂ → ℂ := fun z => f a k ε (ω₀ + z) + S z
  have hwlow : ∀ z ∈ closedBall (0 : ℂ) ρ, P - T ≤ ‖w z‖ := by
    intro z hz
    have hzn : ‖z‖ ≤ ρ := by simpa using hz
    have him : (w z).im = ω₀.im + z.im + P := by simp [w]
    have h1 : |ω₀.im| ≤ ‖ω₀‖ := Complex.abs_im_le_norm ω₀
    have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have h3 : |(w z).im| ≤ ‖w z‖ := Complex.abs_im_le_norm _
    have h4 : -|ω₀.im| ≤ ω₀.im := neg_abs_le _
    have h5 : -|z.im| ≤ z.im := neg_abs_le _
    have h6 : (w z).im ≤ |(w z).im| := le_abs_self _
    linarith
  have hwpos : ∀ z ∈ closedBall (0 : ℂ) ρ, 0 < ‖w z‖ := by
    intro z hz
    have := hwlow z hz
    have : 0 < P - T := by linarith
    linarith [hwlow z hz]
  have hSb : ∀ z ∈ closedBall (0 : ℂ) ρ, ‖S z‖ < μ / 2 := by
    intro z hz
    have hzn : ‖z‖ ≤ ρ := by simpa using hz
    have hlow := hwlow z hz
    have hPT : 0 < P - T := by linarith
    -- exponential bound
    have hre : |(w z).re| ≤ T := by
      have : (w z).re = ω₀.re + z.re := by simp [w]
      rw [this]
      have h1 : |ω₀.re| ≤ ‖ω₀‖ := Complex.abs_re_le_norm ω₀
      have h2 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      calc |ω₀.re + z.re| ≤ |ω₀.re| + |z.re| := abs_add_le _ _
        _ ≤ T := by rw [hT]; linarith
    have hexp : ‖Complex.exp (-2 * w z)‖ ≤ Real.exp (2 * T) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have : (-2 * w z).re = -2 * (w z).re := by simp
      rw [this]
      have := neg_abs_le (w z).re
      have := le_abs_self (w z).re
      linarith
    have hnum : ‖(a : ℂ) * (1 + (K a : ℂ) * Complex.exp (-2 * w z))‖ ≤ B := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha]
      apply mul_le_mul_of_nonneg_left _ ha
      calc ‖1 + (K a : ℂ) * Complex.exp (-2 * w z)‖
          ≤ ‖(1 : ℂ)‖ + ‖(K a : ℂ) * Complex.exp (-2 * w z)‖ := norm_add_le _ _
        _ ≤ 1 + Real.exp (2 * T) := by
          rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK0.le]
          have : K a * ‖Complex.exp (-2 * w z)‖ ≤ 1 * Real.exp (2 * T) :=
            mul_le_mul hK1 hexp (norm_nonneg _) zero_le_one
          linarith
    simp only [S]
    rw [norm_div]
    have hwp := hwpos z hz
    rw [div_lt_iff₀ hwp]
    have : B < μ / 2 * (P - T) := by
      have h3 : 2 * B / μ < P - T := by linarith
      rw [div_lt_iff₀ hμ] at h3
      linarith
    calc ‖(a : ℂ) * (1 + (K a : ℂ) * Complex.exp (-2 * w z))‖ ≤ B := hnum
      _ < μ / 2 * (P - T) := this
      _ ≤ μ / 2 * ‖w z‖ := by apply mul_le_mul_of_nonneg_left hlow (by positivity)
  have hdiffS : DifferentiableOn ℂ G (closedBall (0 : ℂ) ρ) := by
    intro z hz
    have hwz : w z ≠ 0 := norm_pos_iff.mp (hwpos z hz)
    have h1 : DifferentiableAt ℂ (fun z => f a k ε (ω₀ + z)) z :=
      ((hdf ε).comp (differentiable_const ω₀ |>.add differentiable_id)) z
    have h2 : DifferentiableAt ℂ S z := by
      simp only [S, w]
      apply DifferentiableAt.div
      · fun_prop
      · fun_prop
      · exact hwz
    exact (h1.add h2).differentiableWithinAt
  have hcl : closure (ball (0 : ℂ) ρ) = closedBall 0 ρ := closure_ball 0 hρ.ne.symm
  have hDC : DiffContOnCl ℂ G (ball (0 : ℂ) ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [hcl]; exact hdiffS
  obtain ⟨z, hz, hGz⟩ := exists_zero_of_norm_lt_on_sphere G 0 ρ hρ hDC (by
    intro y hy
    have hy' : y ∈ closedBall (0 : ℂ) ρ := sphere_subset_closedBall hy
    have h0 : G 0 = S 0 := by simp only [G]; simp [hf0]
    have hS0 := hSb 0 (mem_closedBall_self hρ.le)
    have hSy := hSb y hy'
    have hfy : μ ≤ ‖f a k ε (ω₀ + y)‖ := by
      apply hsph
      rw [mem_sphere, dist_eq_norm]; simpa using hy
    have : ‖f a k ε (ω₀ + y)‖ - ‖S y‖ ≤ ‖G y‖ := by
      have := norm_sub_norm_le (f a k ε (ω₀ + y)) (-(S y))
      simp only [G]
      rw [sub_neg_eq_add, norm_neg] at this
      exact this
    rw [h0]; linarith)
  have hzc : z ∈ closedBall (0 : ℂ) ρ := ball_subset_closedBall hz
  have hwz : w z ≠ 0 := norm_pos_iff.mp (hwpos z hzc)
  refine ⟨j, hNj, w z, ?_, ?_⟩
  · have : w z - (ω₀ + ((j : ℝ) * p : ℝ) * I) = z := by simp only [w, hP]; ring
    rw [this]
    have : ‖z‖ < ρ := by simpa using hz
    linarith
  · have hfz : f a k ε (w z) = f a k ε (ω₀ + z) := f_periodic_iter a k ε p hper j (ω₀ + z)
    have hG : f a k ε (ω₀ + z) + S z = 0 := hGz
    simp only [S] at hG
    unfold h
    rw [hfz]
    have : w z * (f a k ε (ω₀ + z) + (a : ℂ) * (1 + (K a : ℂ) * Complex.exp (-2 * w z)) / w z) = 0 := by
      rw [hG, mul_zero]
    rw [mul_add, mul_div_cancel₀ _ hwz] at this
    exact this

theorem key_identity (a k ε : ℝ) (ω : ℂ) :
    ((a : ℂ) + ω) * Complex.cosh ((a : ℂ) + ω)
      + (k : ℂ) * ω * Complex.exp (-(ε : ℂ) * ω) * Complex.sinh ((a : ℂ) + ω)
      = Complex.exp ((a : ℂ) + ω) / 2 * h a k ε ω := by
  have hK : (K a : ℂ) = Complex.exp (-2 * (a : ℂ)) := by
    unfold K; rw [Complex.ofReal_exp]; push_cast; ring_nf
  have hq : Complex.exp (-((a : ℂ) + ω))
      = Complex.exp ((a : ℂ) + ω) * ((K a : ℂ) * Complex.exp (-2 * ω)) := by
    rw [hK, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  unfold h f
  simp only [Complex.cosh, Complex.sinh]
  rw [hq]
  ring

theorem const_of_hasDeriv_zero (V V' : ℝ → ℂ) (hV : ∀ x, HasDerivAt V (V' x) x)
    (h0 : ∀ x ∈ Icc (0 : ℝ) 1, V' x = 0) : ∀ x ∈ Icc (0 : ℝ) 1, V x = V 0 := by
  apply constant_of_derivWithin_zero
  · intro x _; exact (hV x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hx
    rw [((hV x).hasDerivWithinAt).derivWithin (uniqueDiffOn_Icc zero_lt_one x hx')]
    exact h0 x hx'

theorem eig_explicit (a k ε : ℝ) (ω : ℂ) (φ : ℝ → ℂ) (hφ : IsEigenpair a k ε ω φ) :
    ∀ x ∈ Icc (0 : ℝ) 1, deriv φ x = deriv φ 0 * Complex.cosh (((a : ℂ) + ω) * x) ∧
      ((a : ℂ) + ω) * φ x = deriv φ 0 * Complex.sinh (((a : ℂ) + ω) * x) := by
  set l : ℂ := (a : ℂ) + ω with hl
  have hC2 : ContDiff ℝ 2 φ := hφ.contDiff
  have hd1 : Differentiable ℝ φ := hC2.differentiable (by norm_num)
  have hdd : Differentiable ℝ (deriv φ) := hC2.differentiable_deriv_two
  have hC1 : ContDiff ℝ 1 (deriv φ) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) φ from hC2)).2.2
  have hcdd : Continuous (deriv (deriv φ)) := hC1.continuous_deriv_one
  have hode : ∀ x ∈ Icc (0 : ℝ) 1, deriv (deriv φ) x = l ^ 2 * φ x := by
    have hEq : EqOn (deriv (deriv φ)) (fun x => l ^ 2 * φ x) (Ioo 0 1) := hφ.ode
    exact hEq.of_subset_closure hcdd.continuousOn
      (continuous_const.mul hd1.continuous).continuousOn Ioo_subset_Icc_self
      (by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)])
  have hlin : ∀ x : ℝ, HasDerivAt (fun x : ℝ => l * (x : ℂ)) l x := by
    intro x
    simpa using ((hasDerivAt_id x).ofReal_comp).const_mul l
  have hch : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.cosh (l * (x : ℂ)))
      (Complex.sinh (l * (x : ℂ)) * l) x := fun x => by
    have := (Complex.hasDerivAt_cosh (l * (x : ℂ))).scomp x (hlin x)
    exact this.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have hsh : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.sinh (l * (x : ℂ)))
      (Complex.cosh (l * (x : ℂ)) * l) x := fun x => by
    have := (Complex.hasDerivAt_sinh (l * (x : ℂ))).scomp x (hlin x)
    exact this.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have hp1 : ∀ x : ℝ, HasDerivAt φ (deriv φ x) x := fun x => (hd1 x).hasDerivAt
  have hp2 : ∀ x : ℝ, HasDerivAt (deriv φ) (deriv (deriv φ) x) x := fun x => (hdd x).hasDerivAt
  have hV := const_of_hasDeriv_zero
    (fun x => deriv φ x * Complex.cosh (l * (x : ℂ)) - l * φ x * Complex.sinh (l * (x : ℂ)))
    (fun x => (deriv (deriv φ) x - l ^ 2 * φ x) * Complex.cosh (l * (x : ℂ)))
    (by
      intro x
      have := ((hp2 x).mul (hch x)).sub (((hp1 x).const_mul l).mul (hsh x))
      exact this.congr_deriv (by ring))
    (by intro x hx; rw [hode x hx]; ring)
  have hW := const_of_hasDeriv_zero
    (fun x => deriv φ x * Complex.sinh (l * (x : ℂ)) - l * φ x * Complex.cosh (l * (x : ℂ)))
    (fun x => (deriv (deriv φ) x - l ^ 2 * φ x) * Complex.sinh (l * (x : ℂ)))
    (by
      intro x
      have := ((hp2 x).mul (hsh x)).sub (((hp1 x).const_mul l).mul (hch x))
      exact this.congr_deriv (by ring))
    (by intro x hx; rw [hode x hx]; ring)
  intro x hx
  have hV0 := hV x hx
  have hW0 := hW x hx
  simp only [Complex.ofReal_zero, mul_zero, Complex.cosh_zero, Complex.sinh_zero, mul_one,
    hφ.left, sub_zero, zero_mul] at hV0 hW0
  have hsq := Complex.cosh_sq (l * (x : ℂ))
  constructor
  · linear_combination (Complex.cosh (l * (x : ℂ))) * hV0 - (Complex.sinh (l * (x : ℂ))) * hW0
      - (deriv φ x) * hsq
  · linear_combination (Complex.sinh (l * (x : ℂ))) * hV0 - (Complex.cosh (l * (x : ℂ))) * hW0
      - (l * φ x) * hsq

theorem sinh_lx_ne_zero (l : ℂ) (hl : l ≠ 0) :
    Complex.sinh (l * ((1 / (‖l‖ + 1) : ℝ) : ℂ)) ≠ 0 := by
  intro h0
  have hn : 0 < ‖l‖ := norm_pos_iff.mpr hl
  have hx : 0 < 1 / (‖l‖ + 1) := by positivity
  have hs : Complex.sin ((l * ((1 / (‖l‖ + 1) : ℝ) : ℂ)) * Complex.I) = 0 := by
    rw [Complex.sin_mul_I, h0, zero_mul]
  obtain ⟨n, hn'⟩ := Complex.sin_eq_zero_iff.mp hs
  have hnorm : ‖(l * ((1 / (‖l‖ + 1) : ℝ) : ℂ)) * Complex.I‖ = ‖l‖ / (‖l‖ + 1) := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hx.le]
    field_simp
  rw [hn'] at hnorm
  have h1 : ‖l‖ / (‖l‖ + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have h2 : ‖((n : ℂ) * (Real.pi : ℂ))‖ = |(n : ℝ)| * Real.pi := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2] at hnorm
  have hn0 : n = 0 := by
    by_contra hne
    have : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hne
      have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
      simpa using this
    nlinarith [Real.pi_gt_three]
  have h3 : l * ((1 / (‖l‖ + 1) : ℝ) : ℂ) * Complex.I = 0 := by rw [hn', hn0]; simp
  have h4 : ((1 / (‖l‖ + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  exact (mul_ne_zero (mul_ne_zero hl h4) Complex.I_ne_zero) h3

theorem eq16_characteristic_equation (a k ε : ℝ) (ha : 0 ≤ a) (hk : 0 ≤ k) (hε : 0 < ε)
    (ω : ℂ) (hω : ω ≠ -(a : ℂ)) :
    ω ∈ delaySpectrum a k ε ↔ h a k ε ω = 0 := by
  have hl : (a : ℂ) + ω ≠ 0 := fun h0 => hω (by linear_combination h0)
  have hexp : Complex.exp ((a : ℂ) + ω) / 2 ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) two_ne_zero
  have hkey := key_identity a k ε ω
  constructor
  · rintro ⟨φ, hφ, x₁, hx₁, hφx₁⟩
    have hexpl := eig_explicit a k ε ω φ hφ
    have hc : deriv φ 0 ≠ 0 := by
      intro hc0
      have := (hexpl x₁ hx₁).2
      rw [hc0, zero_mul] at this
      exact hφx₁ ((mul_eq_zero.mp this).resolve_left hl)
    obtain ⟨d1, e1⟩ := hexpl 1 ⟨zero_le_one, le_rfl⟩
    simp only [Complex.ofReal_one, mul_one] at d1 e1
    have hb := hφ.right
    have : deriv φ 0 * (Complex.exp ((a : ℂ) + ω) / 2 * h a k ε ω) = 0 := by
      rw [← hkey]
      linear_combination ((a : ℂ) + ω) * hb - ((a : ℂ) + ω) * d1
        - ((k : ℂ) * ω * Complex.exp (-(ε : ℂ) * ω)) * e1
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hc
    · exact (mul_eq_zero.mp h1).resolve_left hexp
  · intro hh
    set l : ℂ := (a : ℂ) + ω with hl'
    have hlin : ∀ x : ℝ, HasDerivAt (fun x : ℝ => l * (x : ℂ)) l x := by
      intro x
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul l
    have hsh : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.sinh (l * (x : ℂ)))
        (l * Complex.cosh (l * (x : ℂ))) x := fun x => by
      have := (Complex.hasDerivAt_sinh (l * (x : ℂ))).scomp x (hlin x)
      exact this.congr_deriv (by simp [smul_eq_mul])
    have hch : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.cosh (l * (x : ℂ)))
        (l * Complex.sinh (l * (x : ℂ))) x := fun x => by
      have := (Complex.hasDerivAt_cosh (l * (x : ℂ))).scomp x (hlin x)
      exact this.congr_deriv (by simp [smul_eq_mul])
    have hd1 : deriv (fun x : ℝ => Complex.sinh (l * (x : ℂ))) = fun x : ℝ => l * Complex.cosh (l * (x : ℂ)) :=
      funext fun x => (hsh x).deriv
    have hd2 : deriv (deriv (fun x : ℝ => Complex.sinh (l * (x : ℂ))))
        = fun x : ℝ => l * (l * Complex.sinh (l * (x : ℂ))) := by
      rw [hd1]; exact funext fun x => ((hch x).const_mul l).deriv
    refine ⟨fun x : ℝ => Complex.sinh (l * (x : ℂ)), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · -- ContDiff
      have h0 : ContDiff ℝ 2 (fun x : ℝ => l * (x : ℂ)) :=
        contDiff_const.mul Complex.ofRealCLM.contDiff
      exact (Complex.contDiff_sinh.restrict_scalars ℝ).comp h0
    · intro x _
      rw [hd2]; ring
    · simp
    · rw [hd1]
      have hh' : l * Complex.cosh l + (k : ℂ) * ω * Complex.exp (-(ε : ℂ) * ω) * Complex.sinh l = 0 := by
        rw [hkey, hh, mul_zero]
      simp only [Complex.ofReal_one, mul_one]
      linear_combination hh'
    · refine ⟨1 / (‖l‖ + 1), ⟨by positivity, ?_⟩, sinh_lx_ne_zero l hl⟩
      rw [div_le_one (by positivity)]
      linarith [norm_nonneg l]

theorem separated_solution (a k ε : ℝ) (ω : ℂ) (φ : ℝ → ℂ)
    (hφ : IsEigenpair a k ε ω φ) :
    IsClassicalSolution a k ε (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) := by
  have hC2 : ContDiff ℝ 2 φ := hφ.contDiff
  have hd1 : Differentiable ℝ φ := hC2.differentiable (by norm_num)
  have hdd : Differentiable ℝ (deriv φ) := hC2.differentiable_deriv_two
  have hlin : ∀ x : ℝ, HasDerivAt (fun x : ℝ => ω * (x : ℂ)) ω x := by
    intro x
    simpa using ((hasDerivAt_id x).ofReal_comp).const_mul ω
  have hexp : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (ω * (s : ℂ)))
      (ω * Complex.exp (ω * (t : ℂ))) t := fun t => by
    have := (Complex.hasDerivAt_exp (ω * (t : ℂ))).scomp t (hlin t)
    exact this.congr_deriv (by simp [smul_eq_mul, mul_comm])
  have hut : ∀ x t : ℝ, ut (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) x t
      = ω * Complex.exp (ω * (t : ℂ)) * φ x := by
    intro x t
    unfold ut
    exact ((hexp t).mul_const (φ x)).deriv
  have hutt : ∀ x t : ℝ, utt (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) x t
      = ω ^ 2 * Complex.exp (ω * (t : ℂ)) * φ x := by
    intro x t
    unfold utt
    have : (fun s => ut (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) x s)
        = fun s : ℝ => (ω * φ x) * Complex.exp (ω * (s : ℂ)) := by
      funext s; rw [hut]; ring
    rw [this, ((hexp t).const_mul (ω * φ x)).deriv]; ring
  have hux : ∀ x t : ℝ, ux (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) x t
      = Complex.exp (ω * (t : ℂ)) * deriv φ x := by
    intro x t
    unfold ux
    exact (((hd1 x).hasDerivAt).const_mul (Complex.exp (ω * (t : ℂ)))).deriv
  have huxx : ∀ x t : ℝ, uxx (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) x t
      = Complex.exp (ω * (t : ℂ)) * deriv (deriv φ) x := by
    intro x t
    unfold uxx
    have : (fun y => ux (fun x t => Complex.exp (ω * (t : ℂ)) * φ x) y t)
        = fun y : ℝ => Complex.exp (ω * (t : ℂ)) * deriv φ y := by
      funext y; rw [hux]
    rw [this]
    exact (((hdd x).hasDerivAt).const_mul (Complex.exp (ω * (t : ℂ)))).deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ 2 (fun p : ℝ × ℝ => Complex.exp (ω * ((p.2 : ℝ) : ℂ))) := by
      have h0 : ContDiff ℝ 2 (fun p : ℝ × ℝ => ω * ((p.2 : ℝ) : ℂ)) :=
        contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)
      have hE : ContDiff ℝ 2 Complex.exp := Complex.contDiff_exp
      exact hE.comp h0
    exact h1.mul (hC2.comp contDiff_fst)
  · intro x hx t _
    rw [hutt, huxx, hut, hφ.ode x hx]
    ring
  · intro t _
    simp [hφ.left]
  · intro t ht
    rw [hux, hut]
    have hr := hφ.right
    have e1 : Complex.exp (ω * (t : ℂ)) = Complex.exp (ω * ((t - ε : ℝ) : ℂ)) * Complex.exp (ω * (ε : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : Complex.exp (ω * (ε : ℂ)) * Complex.exp (-(ε : ℂ) * ω) = 1 := by
      rw [← Complex.exp_add]; rw [show ω * (ε : ℂ) + -(ε : ℂ) * ω = 0 by ring]; simp
    have hd : deriv φ 1 = -((k : ℂ) * ω * Complex.exp (-(ε : ℂ) * ω) * φ 1) := by
      linear_combination hr
    rw [hd, e1]
    linear_combination (-(k : ℂ) * ω * Complex.exp (ω * ((t - ε : ℝ) : ℂ)) * φ 1) * e2

theorem exp_odd_pi (j : ℕ) :
    Complex.exp (-((2 * (j : ℂ) + 1) * (Real.pi : ℂ) * Complex.I)) = -1 := by
  have h : -((2 * (j : ℂ) + 1) * (Real.pi : ℂ) * Complex.I)
      = ((-(j : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + -((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem eq15_delays_dense :
    Set.Ioi (0 : ℝ) ⊆
      closure {ε : ℝ | ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧
            ε = 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1)} := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [Metric.mem_closure_iff]
  intro e he
  obtain ⟨n, hn⟩ := exists_nat_gt (4 / e + 2 / x + 1)
  have h4e : 0 ≤ 4 / e := by positivity
  have h2x : 0 ≤ 2 / x := by positivity
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by linarith
  set t : ℝ := (x * (2 * (n : ℝ) + 1) / 2 - 1) / 2 with ht
  have hxn : 2 < x * (2 * (n : ℝ) + 1) := by
    have : 2 / x < n := by linarith
    rw [div_lt_iff₀ hx0] at this
    nlinarith
  have htpos : 0 < t := by rw [ht]; linarith
  set m : ℕ := ⌈t⌉₊ with hm
  have hm1 : t ≤ (m : ℝ) := Nat.le_ceil t
  have hm2 : (m : ℝ) < t + 1 := Nat.ceil_lt_add_one htpos.le
  have hmge : 1 ≤ m := by
    rw [hm]; exact Nat.one_le_iff_ne_zero.mpr (by
      intro h; rw [Nat.ceil_eq_zero] at h; linarith)
  refine ⟨2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1), ⟨m, n, hmge, by exact_mod_cast (show (1:ℝ) ≤ n from hn1), rfl⟩, ?_⟩
  rw [Real.dist_eq, abs_lt]
  have hen : 4 / (2 * (n : ℝ) + 1) < e := by
    rw [div_lt_iff₀ hnpos]
    have : 4 / e < n := by linarith
    rw [div_lt_iff₀ he] at this
    nlinarith
  have key1 : x ≤ 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) := by
    rw [le_div_iff₀ hnpos]; rw [ht] at hm1; linarith
  have key2 : 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) < x + 4 / (2 * (n : ℝ) + 1) := by
    have : x + 4 / (2 * (n : ℝ) + 1) = (x * (2 * (n : ℝ) + 1) + 4) / (2 * (n : ℝ) + 1) := by
      field_simp
    rw [this, div_lt_div_iff_of_pos_right hnpos]
    rw [ht] at hm2; linarith
  constructor <;> linarith

theorem eq12_15_root_above_threshold (a k : ℝ) (ha : 0 ≤ a)
    (hkK : (1 - K a) / (1 + K a) < k) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    ∃ ω₁ : ℝ, 0 < ω₁ ∧
      f a k (2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1))
        ((ω₁ : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2) = 0 := by
  set ε : ℝ := 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) with hε
  have hK0 := K_pos a
  have hk0 : (1 - K a) < k * (1 + K a) := (div_lt_iff₀ (by positivity : 0 < 1 + K a)).mp hkK
  set g : ℝ → ℝ := fun x => (1 - K a * Real.exp (-2 * x))
    - k * Real.exp (-ε * x) * (1 + K a * Real.exp (-2 * x)) with hg
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hg0 : g 0 < 0 := by simp only [hg]; simp; linarith
  have e1 : Filter.Tendsto (fun x : ℝ => Real.exp (-2 * x)) Filter.atTop (nhds 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa [Function.comp_def, neg_mul] using this
  have hεpos : 0 < ε := by rw [hε]; positivity
  have e2 : Filter.Tendsto (fun x : ℝ => Real.exp (-ε * x)) Filter.atTop (nhds 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.tendsto_id.const_mul_atTop hεpos)
    simpa [Function.comp_def, neg_mul] using this
  have hlim : Filter.Tendsto g Filter.atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub ((tendsto_const_nhds (x := K a)).mul e1) |>.sub
      (((tendsto_const_nhds (x := k)).mul e2).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_nhds (x := K a)).mul e1)))
    have h1 : (1 - K a * 0 - k * 0 * (1 + K a * 0)) = 1 := by ring
    rw [h1] at this
    exact this
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp (hlim.eventually (lt_mem_nhds (zero_lt_one' ℝ)))
  have hX' := hX (max X 1) (le_max_left _ _)
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc (le_trans zero_le_one (le_max_right X 1))
    hgc.continuousOn ⟨hg0.le, hX'.le⟩
  have hxpos : 0 < x := by
    rcases hx.1.eq_or_lt with h0 | h0
    · rw [← h0] at hgx; linarith
    · exact h0
  refine ⟨x, hxpos, ?_⟩
  have c1 : Complex.exp (-2 * ((x : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2))
      = -((Real.exp (-2 * x) : ℝ) : ℂ) := by
    have : -2 * ((x : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2)
        = ((-2 * x : ℝ) : ℂ) + (-((2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I)) := by
      push_cast; ring
    rw [this, Complex.exp_add, exp_odd_pi n, ← Complex.ofReal_exp]; ring
  have c2 : Complex.exp (-(ε : ℂ) * ((x : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2))
      = -((Real.exp (-ε * x) : ℝ) : ℂ) := by
    have hn0 : (2 * (n : ℂ) + 1) ≠ 0 := by
      have : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      exact_mod_cast this
    have : -(ε : ℂ) * ((x : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2)
        = ((-ε * x : ℝ) : ℂ) + (-((2 * (m : ℂ) + 1) * (Real.pi : ℂ) * Complex.I)) := by
      rw [hε]; push_cast; field_simp; ring
    rw [this, Complex.exp_add, exp_odd_pi m, ← Complex.ofReal_exp]; ring
  have hf : f a k ε ((x : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2)
      = ((g x : ℝ) : ℂ) := by
    unfold f
    rw [c1, c2]
    simp only [hg]
    push_cast
    ring
  rw [hf, hgx]; simp

theorem exists_inner_point (φ : ℝ → ℂ) (hφ : Continuous φ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
    (hne : φ x ≠ 0) : ∃ x₀ ∈ Ioo (0 : ℝ) 1, φ x₀ ≠ 0 := by
  have hU : IsOpen (φ ⁻¹' {(0 : ℂ)}ᶜ) := isOpen_compl_singleton.preimage hφ
  have hcl : x ∈ closure (Ioo (0 : ℝ) 1) := by rw [closure_Ioo (by norm_num)]; exact hx
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hcl _ hU (by simpa using hne)
  exact ⟨y, hy2, by simpa using hy1⟩

theorem unstable_of_spectrum (a k ε : ℝ) (ha : 0 ≤ a) (hk : 0 ≤ k) (hε : 0 < ε) (ω : ℂ)
    (hre : 0 < ω.re) (hh : h a k ε ω = 0) :
    ∃ u : ℝ → ℝ → ℂ, IsExpUnstableSolution a k ε u := by
  have hω : ω ≠ -(a : ℂ) := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  obtain ⟨φ, hφ, x, hx, hne⟩ := (eq16_characteristic_equation a k ε ha hk hε ω hω).mpr hh
  obtain ⟨x₀, hx₀, hne₀⟩ := exists_inner_point φ hφ.contDiff.continuous x hx hne
  refine ⟨_, separated_solution a k ε ω φ hφ, ω.re, hre, ‖φ x₀‖, norm_pos_iff.mpr hne₀, x₀, hx₀, ?_⟩
  intro t _
  show ‖φ x₀‖ * Real.exp (ω.re * t) ≤ ‖Complex.exp (ω * (t : ℂ)) * φ x₀‖
  rw [norm_mul, Complex.norm_exp]
  have : (ω * (t : ℂ)).re = ω.re * t := by simp
  rw [this, mul_comm]

theorem solution (a k : ℝ) (ha : 0 ≤ a)
    (hkK : (1 - K a) / (1 + K a) < k) :
    ∃ D : Set ℝ, IsOpenDenseInPos D ∧
      ∀ ε ∈ D, ∃ u : ℝ → ℝ → ℂ, IsExpUnstableSolution a k ε u := by
  have hK0 := K_pos a
  have hK1 := K_le_one a ha
  have hk0 : 0 ≤ k := by
    have : 0 ≤ (1 - K a) / (1 + K a) := div_nonneg (by linarith) (by linarith)
    linarith
  obtain ⟨hfc, hhc, hdf, hdh, hpos⟩ := f_h_regular a k ha hk0
  have key : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∃ η : ℝ, 0 < η ∧
      ∀ ε : ℝ, |ε - 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1)| < η →
        ∃ ω : ℂ, 0 < ω.re ∧ h a k ε ω = 0 := by
    intro m n hm hn
    set e0 : ℝ := 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) with he0
    obtain ⟨ω₁, hω₁, hz⟩ := eq12_15_root_above_threshold a k ha hkK m n hm hn
    set ω₀ : ℂ := (ω₁ : ℂ) + (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2 with hω₀
    have hp : 0 < (2 * (n : ℝ) + 1) * Real.pi := by positivity
    obtain ⟨j, -, ω', hω'1, hω'2⟩ := h_zero_near_f_zero_translates a k e0 ha hk0 ω₀ hz
      ((2 * (n : ℝ) + 1) * Real.pi) hp (fun ω => f_periodic_rational_delay a k m n ω)
      (ω₁ / 2) (by positivity) 0
    have hre0 : (ω₀ + (((j : ℝ) * ((2 * (n : ℝ) + 1) * Real.pi) : ℝ) : ℂ) * Complex.I).re = ω₁ := by
      simp [hω₀]
    have hre : ω₁ / 2 < ω'.re := by
      have h1 := Complex.abs_re_le_norm (ω' - (ω₀ + (((j : ℝ) * ((2 * (n : ℝ) + 1) * Real.pi) : ℝ) : ℂ) * Complex.I))
      rw [Complex.sub_re, hre0] at h1
      have h2 := neg_abs_le (ω'.re - ω₁)
      linarith
    have hrepos : 0 < ω'.re := by linarith
    obtain ⟨η, hη, hηp⟩ := zero_persists (h a k) hhc hdh e0 ω' hω'2
      ⟨((1 : ℝ) : ℂ), (hpos e0 1 one_pos).2⟩ ω'.re hrepos
    refine ⟨η, hη, fun ε hε => ?_⟩
    obtain ⟨ω, hω, hω0⟩ := hηp ε hε
    refine ⟨ω, ?_, hω0⟩
    have h1 := Complex.abs_re_le_norm (ω - ω')
    rw [Complex.sub_re] at h1
    have h2 : ‖ω - ω'‖ < ω'.re := by rwa [mem_ball, dist_eq_norm] at hω
    have h3 := neg_abs_le (ω.re - ω'.re)
    linarith
  choose! η hη0 hη using key
  set e : ℕ → ℕ → ℝ := fun m n => 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) with he
  have epos : ∀ m n : ℕ, 0 < e m n := fun m n => by simp only [he]; positivity
  set D : Set ℝ := Ioi 0 ∩ ⋃ m : ℕ, ⋃ n : ℕ, ⋃ (_ : 1 ≤ m), ⋃ (_ : 1 ≤ n),
    Metric.ball (e m n) (η m n) with hD
  have hmemD : ∀ ε, ε ∈ D ↔ 0 < ε ∧ ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ |ε - e m n| < η m n := by
    intro ε
    simp only [hD, mem_inter_iff, mem_Ioi, mem_iUnion, Metric.mem_ball, Real.dist_eq, exists_prop]
  refine ⟨D, ⟨?_, inter_subset_left, ?_⟩, ?_⟩
  · exact isOpen_Ioi.inter (isOpen_iUnion fun m => isOpen_iUnion fun n =>
      isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball)
  · refine eq15_delays_dense.trans (closure_mono ?_)
    rintro ε ⟨m, n, hm, hn, rfl⟩
    exact (hmemD _).mpr ⟨epos m n, m, n, hm, hn, by
      rw [show (2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1)) = e m n from rfl, sub_self, abs_zero]
      exact hη0 m n hm hn⟩
  · intro ε hεD
    obtain ⟨hε0, m, n, hm, hn, hlt⟩ := (hmemD ε).mp hεD
    obtain ⟨ω, hre, hω⟩ := hη m n hm hn ε hlt
    exact unstable_of_spectrum a k ε ha hk0 hε0 ω hre hω

end
