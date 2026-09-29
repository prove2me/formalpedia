-- Prove2me | solution 1 for DeBruijnNewman.Dobner.zeta_zero_disk
-- status  : ACCEPTED   (prove)
-- author  : @adobner
-- created : 2026-09-24T22:15:15.843293+00:00
-- url     : https://prove2.me/submissions/93a3f3b0-b6e1-40a6-9ec2-6efa1073ac16

import Definitions.Def_DeBruijnNewman_Dobner

open Filter Metric Set
open scoped Topology

/-!
Dobner's zero-existence argument for the Gaussian-damped zeta series.
The square-completion estimate gives an entire function of order at most
two. In the zero-free case, harmonicity of log |f|, a harmonic conjugate,
Borel–Carathéodory, and Cauchy's estimate imply that log |f| on the real
axis is a quadratic polynomial. Its limit at +∞ contradicts its value at 0.
-/

private noncomputable def weight (t a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (t / 4 * Real.log ((n : ℝ) + 1) ^ 2
    - a * Real.log ((n : ℝ) + 1))

private noncomputable def term (t : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp
    (((t / 4 * Real.log ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ)
      - s * (Real.log ((n : ℝ) + 1) : ℂ))

private theorem weight_pos (t a : ℝ) (n : ℕ) : 0 < weight t a n :=
  Real.exp_pos _

private theorem pseries_summable :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
  have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) 1).mpr h0

private theorem weight_bound (t a : ℝ) (ht : t < 0) (n : ℕ) :
    weight t a n ≤
      Real.exp ((a - 2) ^ 2 / (-t)) * ((n : ℝ) + 1) ^ (-2 : ℝ) := by
  unfold weight
  rw [Real.rpow_def_of_pos (by positivity : 0 < (n : ℝ) + 1), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hquad :
      t / 4 * Real.log ((n : ℝ) + 1) ^ 2
        + (2 - a) * Real.log ((n : ℝ) + 1) ≤ (a - 2) ^ 2 / (-t) := by
    apply (le_div_iff₀ (neg_pos.mpr ht)).mpr
    nlinarith [sq_nonneg (t / 2 * Real.log ((n : ℝ) + 1) + (2 - a))]
  linarith

private theorem weights_summable (t a : ℝ) (ht : t < 0) :
    Summable (weight t a) := by
  apply (pseries_summable.mul_left (Real.exp ((a - 2) ^ 2 / (-t)))).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_pos (weight_pos t a n)]
  exact weight_bound t a ht n

private theorem term_norm (t : ℝ) (s : ℂ) (n : ℕ) :
    ‖term t s n‖ = weight t s.re n := by
  unfold term weight
  rw [Complex.norm_exp]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, mul_zero, sub_zero]

private theorem term_norm_bound (t a : ℝ) (s : ℂ) (hs : a ≤ s.re) (n : ℕ) :
    ‖term t s n‖ ≤ weight t a n := by
  rw [term_norm]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))
  nlinarith

private theorem series_entire (t : ℝ) (ht : t < 0) :
    Differentiable ℂ (DeBruijnNewman.Dobner.zetaT t) := by
  intro s
  let U : Set ℂ := {z | s.re - 1 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hs : s ∈ U := by dsimp [U]; linarith
  have hdiff : DifferentiableOn ℂ (DeBruijnNewman.Dobner.zetaT t) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm
      (weights_summable t (s.re - 1) ht)
    · intro n
      fun_prop
    · exact hU
    · intro n z hz
      exact term_norm_bound t (s.re - 1) z (le_of_lt hz) n
  exact hdiff.differentiableAt (hU.mem_nhds hs)

private theorem series_real (t x : ℝ) :
    DeBruijnNewman.Dobner.zetaT t (x : ℂ) = (∑' n, weight t x n : ℝ) := by
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp [weight, Complex.ofReal_exp]

private theorem series_zero_gt_one (t : ℝ) (ht : t < 0) :
    1 < ‖DeBruijnNewman.Dobner.zetaT t 0‖ := by
  have hw := weights_summable t 0 ht
  have hpos : ∀ n, 0 < weight t 0 n := fun _ => Real.exp_pos _
  have hsum : 1 < ∑' n, weight t 0 n := by
    have hle := hw.sum_le_tsum (Finset.range 2) (fun n _ => (hpos n).le)
    have h1 := hpos 1
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at hle
    have h0 : weight t 0 0 = 1 := by simp [weight]
    rw [h0] at hle
    linarith
  simpa only [← Complex.ofReal_zero, series_real, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (lt_trans zero_lt_one hsum)] using hsum

private theorem series_tendsto_one (t : ℝ) (ht : t < 0) :
    Tendsto (fun x : ℝ => DeBruijnNewman.Dobner.zetaT t (x : ℂ)) atTop (𝓝 1) := by
  have hlim (n : ℕ) :
      Tendsto (fun x : ℝ => weight t x n) atTop
        (𝓝 (if n = 0 then (1 : ℝ) else 0)) := by
    by_cases hn : n = 0
    · subst n
      simp [weight]
    · rw [if_neg hn]
      have hlog : 0 < Real.log ((n : ℝ) + 1) := by
        apply Real.log_pos
        have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        linarith
      apply Real.tendsto_exp_atBot.comp
      simpa only [sub_eq_add_neg, Function.comp_def, id_eq] using
        tendsto_atBot_add_const_left atTop
        (t / 4 * Real.log ((n : ℝ) + 1) ^ 2)
        (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hlog))
  have hdom : ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, ‖weight t x n‖ ≤ weight t 0 n := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx n
    rw [Real.norm_eq_abs, abs_of_pos (weight_pos t x n)]
    simpa only [term_norm, Complex.ofReal_re] using
      term_norm_bound t 0 (x : ℂ) hx n
  have h := tendsto_tsum_of_dominated_convergence (weights_summable t 0 ht) hlim hdom
  have hreal : Tendsto (fun x : ℝ => ∑' n, weight t x n) atTop (𝓝 1) := by
    simpa using h
  simpa only [series_real, Complex.ofReal_one, Function.comp_def] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp hreal

private theorem series_norm_bound (t : ℝ) (ht : t < 0) (s : ℂ) :
    ‖DeBruijnNewman.Dobner.zetaT t s‖ ≤
      Real.exp ((s.re - 2) ^ 2 / (-t)) *
        ∑' n : ℕ, ((n : ℝ) + 1) ^ (-2 : ℝ) := by
  have h := tsum_of_norm_bounded
    (pseries_summable.mul_left (Real.exp ((s.re - 2) ^ 2 / (-t)))).hasSum
    (fun n => (term_norm t s n).le.trans (weight_bound t s.re ht n))
  simpa only [tsum_mul_left, term, DeBruijnNewman.Dobner.zetaT] using h

private theorem series_log_norm_bound (t : ℝ) (ht : t < 0)
    (hne : ∀ s, DeBruijnNewman.Dobner.zetaT t s ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ,
      Real.log ‖DeBruijnNewman.Dobner.zetaT t s‖ ≤ C * (1 + ‖s‖) ^ 2 := by
  let S : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-2 : ℝ)
  have hS : 1 ≤ S := by
    simpa [S] using pseries_summable.le_tsum 0
      (fun n _ => Real.rpow_nonneg (by positivity) _)
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg hS
  have hneg : 0 < -t := neg_pos.mpr ht
  refine ⟨Real.log S + 4 / (-t) + 1, by positivity, ?_⟩
  intro s
  have hlog : Real.log ‖DeBruijnNewman.Dobner.zetaT t s‖ ≤
      (s.re - 2) ^ 2 / (-t) + Real.log S := by
    have h := Real.log_le_log (norm_pos_iff.mpr (hne s)) (series_norm_bound t ht s)
    simpa only [Real.log_mul (Real.exp_ne_zero _) hSpos.ne', Real.log_exp, S] using h
  have hre : s.re ^ 2 ≤ ‖s‖ ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg s.re) (norm_nonneg s)).mpr (Complex.abs_re_le_norm s)
  have hsquare : (s.re - 2) ^ 2 ≤ 4 * (1 + ‖s‖) ^ 2 := by
    have := (abs_le.mp (Complex.abs_re_le_norm s)).1
    nlinarith [norm_nonneg s]
  have hK : (s.re - 2) ^ 2 / (-t) ≤ (4 / (-t)) * (1 + ‖s‖) ^ 2 := by
    calc
      _ ≤ (4 * (1 + ‖s‖) ^ 2) / (-t) :=
        (div_le_div_iff_of_pos_right (neg_pos.mpr ht)).mpr hsquare
      _ = _ := by ring
  have hsquare_one : 1 ≤ (1 + ‖s‖) ^ 2 := by nlinarith [norm_nonneg s]
  have hlogS' := mul_le_mul_of_nonneg_left hsquare_one hlogS
  nlinarith

private theorem norm_growth_of_re_growth (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (C : ℝ) (hC : 0 < C) (hbound : ∀ z, (g z).re ≤ C * (1 + ‖z‖) ^ 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ z, ‖g z‖ ≤ D * (1 + ‖z‖) ^ 2 := by
  refine ⟨18 * C + 3 * ‖g 0‖, by positivity, ?_⟩
  intro z
  let R : ℝ := 2 * (1 + ‖z‖)
  let M : ℝ := C * (1 + R) ^ 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hz : z ∈ ball 0 R := by
    rw [mem_ball_zero_iff]
    dsimp [R]
    linarith [norm_nonneg z]
  have hmaps : MapsTo g (ball 0 R) {w : ℂ | w.re ≤ M} := by
    intro w hw
    apply (hbound w).trans
    dsimp [M]
    gcongr
    exact (mem_ball_zero_iff.mp hw).le
  have hbc := Complex.borelCaratheodory hM hg.differentiableOn hmaps hR hz
  have hden : 0 < R - ‖z‖ := sub_pos.mpr (mem_ball_zero_iff.mp hz)
  have hfirst : 2 * M * ‖z‖ / (R - ‖z‖) ≤ 2 * M := by
    apply (div_le_iff₀ hden).mpr
    dsimp [R]
    nlinarith
  have hsecond : ‖g 0‖ * (R + ‖z‖) / (R - ‖z‖) ≤ 3 * ‖g 0‖ := by
    apply (div_le_iff₀ hden).mpr
    dsimp [R]
    nlinarith [norm_nonneg (g 0)]
  have hMbound : M ≤ 9 * C * (1 + ‖z‖) ^ 2 := by
    dsimp [M, R]
    calc
      _ ≤ C * (9 * (1 + ‖z‖) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        nlinarith [norm_nonneg z]
      _ = _ := by ring
  have hsquare : 1 ≤ (1 + ‖z‖) ^ 2 := by nlinarith [norm_nonneg z]
  have hzero := mul_le_mul_of_nonneg_left hsquare (norm_nonneg (g 0))
  nlinarith

private theorem third_derivative_zero_of_growth (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (D : ℝ) (hD : 0 < D) (hbound : ∀ z, ‖g z‖ ≤ D * (1 + ‖z‖) ^ 2) :
    ∀ c, iteratedDeriv 3 g c = 0 := by
  intro c
  have hle : ∀ᶠ R : ℝ in atTop, ‖iteratedDeriv 3 g c‖ ≤ 54 * D / R := by
    filter_upwards [eventually_ge_atTop (max 1 ‖c‖)] with R hR
    have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
    have hcR : ‖c‖ ≤ R := (le_max_right _ _).trans hR
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
    have hsphere : ∀ z ∈ sphere c R, ‖g z‖ ≤ 9 * D * R ^ 2 := by
      intro z hz
      have hzc : ‖z - c‖ = R := mem_sphere_iff_norm.mp hz
      have hzR : ‖z‖ ≤ 2 * R := by
        have := norm_le_norm_sub_add z c
        rw [hzc] at this
        linarith
      apply (hbound z).trans
      calc
        _ ≤ D * (9 * R ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hD.le
          nlinarith [norm_nonneg z]
        _ = _ := by ring
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      3 hRpos hg.diffContOnCl hsphere
    convert h using 1
    norm_num
    field_simp
    ring
  have hlim : Tendsto (fun R : ℝ => 54 * D / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto tendsto_const_nhds hlim hle)

private theorem affine_of_derivative_const (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a : ℂ) (ha : ∀ z, deriv f z = a) :
    ∀ z, f z = a * z + f 0 := by
  have hd (z : ℂ) : HasDerivAt (fun w => f w - a * w) 0 z := by
    simpa only [ha, mul_one, sub_self] using!
      ((hf z).hasDerivAt.sub ((hasDerivAt_id z).const_mul a))
  intro z
  have h := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) z 0
  simp only [mul_zero, sub_zero] at h
  linear_combination h

private theorem quadratic_of_third_derivative_zero (g : ℂ → ℂ)
    (hg : Differentiable ℂ g) (h3 : ∀ z, iteratedDeriv 3 g z = 0) :
    ∃ a b c : ℂ, ∀ z, g z = a * z ^ 2 + b * z + c := by
  let A : ℂ := deriv (deriv g) 0
  let B : ℂ := deriv g 0
  have h2 (z : ℂ) : deriv (deriv g) z = A :=
    is_const_of_deriv_eq_zero hg.deriv.deriv
      (fun w => by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using h3 w) z 0
  have h1 (z : ℂ) : deriv g z = A * z + B :=
    affine_of_derivative_const (deriv g) hg.deriv A h2 z
  let P : ℂ → ℂ := fun z => (A / 2) * z ^ 2 + B * z
  have hP (z : ℂ) : HasDerivAt P (A * z + B) z := by
    convert! (((hasDerivAt_id z).pow 2).const_mul (A / 2)).add
      ((hasDerivAt_id z).const_mul B) using 1
    simp only [id_eq]
    ring
  have hd (z : ℂ) : HasDerivAt (fun w => g w - P w) 0 z := by
    simpa only [h1, sub_self] using! ((hg z).hasDerivAt.sub (hP z))
  refine ⟨A / 2, B, g 0, fun z => ?_⟩
  have h := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt)
    (fun w => (hd w).deriv) z 0
  simp only [P, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, sub_zero] at h
  linear_combination h

private theorem quadratic_constant_of_tendsto (A B C : ℝ)
    (h : Tendsto (fun x : ℝ => A * x ^ 2 + B * x + C) atTop (𝓝 0)) :
    C = 0 := by
  let p : Polynomial ℝ := Polynomial.C A * Polynomial.X ^ 2 +
    Polynomial.C B * Polynomial.X + Polynomial.C C
  have hp : Tendsto (fun x : ℝ => p.eval x) atTop (𝓝 0) := by simpa [p] using h
  have hdeg : p.degree ≤ 0 := by
    by_contra hn
    have hnorm := p.tendsto_norm_atTop (lt_of_not_ge hn) tendsto_norm_atTop_atTop
    exact not_tendsto_nhds_of_tendsto_atTop hnorm _ hp.norm
  have heval (x : ℝ) : p.eval x = C := by
    rw [p.eq_C_of_degree_le_zero hdeg]
    simp [p]
  have hC : Tendsto (fun _ : ℝ => C) atTop (𝓝 0) := by simpa only [heval] using hp
  exact tendsto_nhds_unique tendsto_const_nhds hC

private theorem series_has_zero (t : ℝ) (ht : t < 0) :
    ∃ c : ℂ, DeBruijnNewman.Dobner.zetaT t c = 0 := by
  by_contra! hne
  let f : ℂ → ℂ := DeBruijnNewman.Dobner.zetaT t
  have hf : Differentiable ℂ f := series_entire t ht
  have hharm : InnerProductSpace.HarmonicOnNhd (fun z => Real.log ‖f z‖) univ :=
    fun z _ => (hf.analyticAt z).harmonicAt_log_norm (hne z)
  obtain ⟨g, hg, hgre⟩ := hharm.exists_analyticOnNhd_univ_re_eq
  have hgd : Differentiable ℂ g := differentiableOn_univ.mp hg.differentiableOn
  obtain ⟨C, hC, hbound⟩ := series_log_norm_bound t ht hne
  have hgbound (z : ℂ) : (g z).re ≤ C * (1 + ‖z‖) ^ 2 := by
    rw [congrFun hgre z]
    exact hbound z
  obtain ⟨D, hD, hnorm⟩ := norm_growth_of_re_growth g hgd C hC hgbound
  obtain ⟨a, b, c, hquad⟩ := quadratic_of_third_derivative_zero g hgd
    (third_derivative_zero_of_growth g hgd D hD hnorm)
  have hlim : Tendsto (fun x : ℝ => Real.log ‖f (x : ℂ)‖) atTop (𝓝 0) := by
    simpa only [norm_one, Real.log_one] using
      ((series_tendsto_one t ht).norm.log (by norm_num : ‖(1 : ℂ)‖ ≠ 0))
  have hpoly : Tendsto (fun x : ℝ => a.re * x ^ 2 + b.re * x + c.re) atTop (𝓝 0) := by
    have heq (x : ℝ) : Real.log ‖f (x : ℂ)‖ = a.re * x ^ 2 + b.re * x + c.re := by
      rw [← congrFun hgre (x : ℂ), hquad]
      simp only [← Complex.ofReal_pow, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    simpa only [heq] using hlim
  have hc : c.re = 0 := quadratic_constant_of_tendsto a.re b.re c.re hpoly
  have hzero : Real.log ‖f 0‖ = 0 := by
    rw [← congrFun hgre 0, hquad]
    simpa using hc
  have hpos : 0 < Real.log ‖f 0‖ := Real.log_pos (series_zero_gt_one t ht)
  linarith

theorem solution (t : ℝ) (ht : t < 0) :
    ∃ (c : ℂ) (r δ : ℝ), 0 < r ∧ 0 < δ ∧
      DeBruijnNewman.Dobner.zetaT t c = 0 ∧
      ∀ s ∈ sphere c r, δ ≤ ‖DeBruijnNewman.Dobner.zetaT t s‖ := by
  obtain ⟨c, hc⟩ := series_has_zero t ht
  let f : ℂ → ℂ := DeBruijnNewman.Dobner.zetaT t
  have hf : Differentiable ℂ f := series_entire t ht
  have hnot : ¬ (∀ᶠ z in 𝓝 c, f z = 0) := by
    intro h
    have heq : f = fun _ => 0 :=
      (hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
        analyticOnNhd_const h
    have hpos : 1 < ‖f 0‖ := series_zero_gt_one t ht
    simp only [heq, norm_zero] at hpos
    linarith
  have hlocal : ∀ᶠ z in 𝓝[≠] c, f z ≠ 0 :=
    (hf.analyticAt c).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnot
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.eventually_iff.mp
    (eventually_nhdsWithin_iff.mp hlocal)
  have hsphere (z : ℂ) (hz : z ∈ sphere c r) : f z ≠ 0 :=
    hball (sphere_subset_closedBall hz) (ne_of_mem_sphere hz hr.ne')
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere c r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hf.continuous.norm.continuousOn
  exact ⟨c, r, ‖f w‖, hr, norm_pos_iff.mpr (hsphere w hw), hc, fun z hz => hmin hz⟩
