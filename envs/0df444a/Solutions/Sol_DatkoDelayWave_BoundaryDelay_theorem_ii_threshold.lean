-- Prove2me | solution 1 for DatkoDelayWave.BoundaryDelay.theorem_ii_threshold
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:23:58.457278+00:00
-- url     : https://prove2.me/submissions/7b94e555-b134-46be-984a-8da75eef03c6

import Mathlib
import Definitions.Def_DatkoDelayWave_BoundaryDelay_DelayedWave

-- carved verbatim out of submission 9e78ff97-3a87-4a96-9f66-6a86542faea0, lines 856-939

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

theorem K_lt_one (a : ℝ) (ha : 0 < a) : K a < 1 := by
  unfold K; rw [Real.exp_lt_one_iff]; linarith

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

theorem critical_h_zero_re_neg (a k ε : ℝ) (ha : 0 < a) (hkK : k = (1 - K a) / (1 + K a))
    (hε : 0 < ε) (ω : ℂ) (hω : h a k ε ω = 0) : ω.re < 0 := by
  by_contra hcon
  push Not at hcon
  have hK0 := K_pos a
  have hK1 := K_lt_one a ha
  have hk0 : k * (1 + K a) = 1 - K a := by rw [hkK]; field_simp
  -- moduli
  set E := Complex.exp (-2 * ω) with hE
  have hEn : ‖E‖ ≤ 1 := by
    rw [hE, Complex.norm_exp]
    rw [Real.exp_le_one_iff]; simp; linarith
  have hKE : ‖(K a : ℂ) * E‖ ≤ K a := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hK0.le]; nlinarith
  have hF : ‖Complex.exp (-(ε : ℂ) * ω)‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]; simp; nlinarith
  have heq : (ω + a) * (1 + (K a : ℂ) * E) = -(ω * (k : ℂ) * Complex.exp (-(ε : ℂ) * ω) * (1 - (K a : ℂ) * E)) := by
    unfold h f at hω
    rw [← hE] at hω
    linear_combination hω
  have n1 : 1 - K a ≤ ‖1 + (K a : ℂ) * E‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-((K a : ℂ) * E))
    simp at this
    calc 1 - K a ≤ 1 - ‖(K a : ℂ) * E‖ := by linarith
      _ ≤ _ := by
        have := norm_sub_norm_le (1 : ℂ) (-((K a : ℂ) * E))
        simpa [sub_neg_eq_add] using this
  have n2 : ‖1 - (K a : ℂ) * E‖ ≤ 1 + K a := by
    calc _ ≤ ‖(1 : ℂ)‖ + ‖(K a : ℂ) * E‖ := norm_sub_le _ _
      _ ≤ 1 + K a := by rw [norm_one]; linarith
  have lhs : (1 - K a) * ‖ω + a‖ ≤ ‖(ω + a) * (1 + (K a : ℂ) * E)‖ := by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right n1 (norm_nonneg _) |>.trans_eq (mul_comm _ _) |> fun h => by nlinarith [norm_nonneg (ω + (a:ℂ))]
  have rhs : ‖(ω + a) * (1 + (K a : ℂ) * E)‖ ≤ ‖ω‖ * (1 - K a) := by
    rw [heq, norm_neg, norm_mul, norm_mul, norm_mul]
    have hkn : ‖(k : ℂ)‖ = k := by
      have : 0 ≤ k := by rw [hkK]; apply div_nonneg <;> linarith
      simp [abs_of_nonneg this]
    rw [hkn]
    have : 0 ≤ k := by rw [hkK]; apply div_nonneg <;> linarith
    calc ‖ω‖ * k * ‖Complex.exp (-(ε : ℂ) * ω)‖ * ‖1 - (K a : ℂ) * E‖ ≤ ‖ω‖ * k * 1 * (1 + K a) := by
          apply mul_le_mul _ n2 (norm_nonneg _) (by positivity)
          apply mul_le_mul_of_nonneg_left hF (by positivity)
      _ = ‖ω‖ * (1 - K a) := by
          have : ‖ω‖ * k * 1 * (1 + K a) = ‖ω‖ * (k * (1 + K a)) := by ring
          rw [this, hk0]
  have hlt : 0 < 1 - K a := by linarith
  have key : ‖ω + a‖ ≤ ‖ω‖ := by
    by_contra hc; push Not at hc
    nlinarith [norm_nonneg ω, norm_nonneg (ω + (a:ℂ))]
  have sq : ‖ω + (a:ℂ)‖ ^ 2 > ‖ω‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp
    nlinarith
  nlinarith [norm_nonneg ω, norm_nonneg (ω + (a:ℂ))]

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

theorem exp_odd_pi (j : ℕ) :
    Complex.exp (-((2 * (j : ℂ) + 1) * (Real.pi : ℂ) * Complex.I)) = -1 := by
  have h : -((2 * (j : ℂ) + 1) * (Real.pi : ℂ) * Complex.I)
      = ((-(j : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + -((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

theorem threshold_explicit_zero (a k : ℝ) (ha : 0 ≤ a)
    (hkK : k = (1 - K a) / (1 + K a)) (m n : ℕ) :
    f a k (2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1))
      ((2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2) = 0 := by
  have hn : (2 * (n : ℂ) + 1) ≠ 0 := by
    have : (2 * (n : ℂ) + 1) = ((2 * n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast (by omega : 2 * n + 1 ≠ 0)
  have h1 : Complex.exp (-2 * ((2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2)) = -1 := by
    rw [← exp_odd_pi n]; congr 1; ring
  have h2 : Complex.exp (-(((2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) : ℝ) : ℂ))
      * ((2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2)) = -1 := by
    rw [← exp_odd_pi m]; congr 1; push_cast; field_simp
  have hK : (1 + K a) ≠ 0 := by unfold K; positivity
  have hKc : (1 + (K a : ℂ)) ≠ 0 := by exact_mod_cast hK
  unfold f
  rw [h1, h2, hkK]
  push_cast
  field_simp
  ring

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

theorem solution (a k : ℝ) (ha : 0 ≤ a) (hk : 0 < k)
    (hkK : k = (1 - K a) / (1 + K a)) :
    (∀ ε > (0 : ℝ), ∀ ω ∈ delaySpectrum a k ε, ω.re < 0) ∧
      ∃ R : Set ℝ, IsCountablyDenseInPos R ∧ ∀ ε ∈ R, ∃ ω : ℕ → ℂ,
        (∀ j, ω j ∈ delaySpectrum a k ε) ∧
          Filter.Tendsto (fun j => (ω j).re) Filter.atTop (nhds 0) := by
  have hK0 := K_pos a
  have h1K : 1 - K a = k * (1 + K a) := by
    rw [hkK]; field_simp
  have hK1 : K a < 1 := by
    have : 0 < k * (1 + K a) := by positivity
    linarith
  have hapos : 0 < a := by
    by_contra hcon
    push Not at hcon
    have h0 : a = 0 := le_antisymm hcon ha
    have : K a = 1 := by simp [K, h0]
    linarith
  refine ⟨?_, ?_⟩
  · intro ε hε ω hω
    by_cases hω0 : ω = -(a : ℂ)
    · rw [hω0]; simp; linarith
    · exact critical_h_zero_re_neg a k ε hapos hkK hε ω
        ((eq16_characteristic_equation a k ε ha hk.le hε ω hω0).mp hω)
  · refine ⟨{ε | ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧ ε = 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1)},
      ⟨?_, ?_, eq15_delays_dense⟩, ?_⟩
    · rintro ε ⟨m, n, -, -, rfl⟩
      show (0 : ℝ) < _
      positivity
    · apply (Set.countable_range
        (fun p : ℕ × ℕ => 2 * (2 * (p.1 : ℝ) + 1) / (2 * (p.2 : ℝ) + 1))).mono
      rintro ε ⟨m, n, -, -, rfl⟩
      exact ⟨(m, n), rfl⟩
    · rintro ε ⟨m, n, hm, hn, rfl⟩
      set ε : ℝ := 2 * (2 * (m : ℝ) + 1) / (2 * (n : ℝ) + 1) with hεdef
      have hεpos : 0 < ε := by rw [hεdef]; positivity
      set p : ℝ := (2 * (n : ℝ) + 1) * Real.pi with hpdef
      have hp : 0 < p := by rw [hpdef]; positivity
      have hp3 : 4 < p / 2 := by
        have : (3 : ℝ) ≤ 2 * (n : ℝ) + 1 := by
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        have := Real.pi_gt_three
        rw [hpdef]; nlinarith
      set base : ℂ := ((p / 2 : ℝ) : ℂ) * Complex.I with hbase
      have hz : f a k ε base = 0 := by
        have : base = (2 * (n : ℂ) + 1) * (Real.pi : ℂ) * Complex.I / 2 := by
          rw [hbase, hpdef]; push_cast; ring
        rw [this]; exact threshold_explicit_zero a k ha hkK m n
      have ex : ∀ N : ℕ, ∃ ω : ℂ, ω ∈ delaySpectrum a k ε ∧ ω.re < 0
          ∧ -(1 / ((N : ℝ) + 1)) < ω.re := by
        intro N
        have hNpos : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
        have hN1 : 1 / ((N : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
        obtain ⟨j, -, ω, hω1, hω2⟩ := h_zero_near_f_zero_translates a k ε ha hk.le base hz p hp
          (fun ω => f_periodic_rational_delay a k m n ω) (1 / ((N : ℝ) + 1)) hNpos 0
        have hre : ω.re < 0 := critical_h_zero_re_neg a k ε hapos hkK hεpos ω hω2
        have hb1 : (base + (((j : ℝ) * p : ℝ) : ℂ) * Complex.I).re = 0 := by simp [hbase]
        have hb2 : (base + (((j : ℝ) * p : ℝ) : ℂ) * Complex.I).im = p / 2 + (j : ℝ) * p := by
          simp [hbase]
        have h1 := Complex.abs_re_le_norm (ω - (base + (((j : ℝ) * p : ℝ) : ℂ) * Complex.I))
        have h2 := Complex.abs_im_le_norm (ω - (base + (((j : ℝ) * p : ℝ) : ℂ) * Complex.I))
        rw [Complex.sub_re, hb1] at h1
        rw [Complex.sub_im, hb2] at h2
        have h3 := neg_abs_le (ω.re - 0)
        have h4 := neg_abs_le (ω.im - (p / 2 + (j : ℝ) * p))
        have hjp : 0 ≤ (j : ℝ) * p := by positivity
        have him : 0 < ω.im := by linarith
        have hne : ω ≠ -(a : ℂ) := by
          intro h0
          have := congrArg Complex.im h0
          simp at this
          linarith
        exact ⟨ω, (eq16_characteristic_equation a k ε ha hk.le hεpos ω hne).mpr hω2, hre, by linarith⟩
      choose ω hω hlt hgt using ex
      refine ⟨ω, hω, ?_⟩
      have hlow : Filter.Tendsto (fun N : ℕ => -(1 / ((N : ℝ) + 1))) Filter.atTop (nhds 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
        (fun N => (hgt N).le) (fun N => (hlt N).le)

end
