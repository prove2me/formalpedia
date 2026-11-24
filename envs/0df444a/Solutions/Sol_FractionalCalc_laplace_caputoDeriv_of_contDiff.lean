-- Prove2me | solution 1 for FractionalCalc.laplace_caputoDeriv_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:48:40.884807+00:00
-- url     : https://prove2.me/submissions/9e79616b-c262-4533-a7ef-7df2725ad6fe

import Mathlib
import Definitions.Def_FractionalCalc_rlIntegral
import Definitions.Def_FractionalCalc_caputoDeriv
import Definitions.Def_QueueingFundamentals_Transient_laplace
import Theorems.Thm_FractionalCalc_laplace_rlIntegral
set_option autoImplicit false
open MeasureTheory Set Classical QueueingFundamentals.Transient
open FractionalCalc
open Filter Topology

private lemma fc3_bound_of_deriv (g g' : ℝ → ℝ) (a C : ℝ) (ha : 0 < a)
    (hg : ∀ t, HasDerivAt g (g' t) t) (hb : ∀ t, 0 ≤ t → |g' t| ≤ C * Real.exp (a * t)) :
    ∀ t, 0 ≤ t → |g t| ≤ (|g 0| + C / a) * Real.exp (a * t) := by
  intro t ht
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary' (f := g) (f' := g') (a := 0) (b := t)
    (B := fun x => |g 0| + C / a * Real.exp (a * x)) (B' := fun x => C * Real.exp (a * x))
    (fun x _ => (hg x).continuousAt.continuousWithinAt)
    (fun x _ => (hg x).hasDerivWithinAt)
    (by
      have hC : 0 ≤ C := by
        have := hb 0 le_rfl
        have h1 : 0 ≤ C * Real.exp (a * 0) := (abs_nonneg _).trans this
        simpa using h1
      simp only [Real.norm_eq_abs, mul_zero, Real.exp_zero, mul_one]
      have : 0 ≤ C / a := div_nonneg hC ha.le
      linarith)
    (by fun_prop)
    (fun x _ => by
      have h1 : HasDerivAt (fun x => |g 0| + C / a * Real.exp (a * x)) (C / a * (Real.exp (a * x) * (a * 1))) x :=
        (((hasDerivAt_id x).const_mul a).exp.const_mul (C / a)).const_add _
      have h2 : C / a * (Real.exp (a * x) * (a * 1)) = C * Real.exp (a * x) := by
        field_simp
      rw [h2] at h1
      exact h1.hasDerivWithinAt)
    (fun x hx => by simpa [Real.norm_eq_abs] using hb x hx.1)
    (x := t) ⟨ht, le_rfl⟩
  simp only [Real.norm_eq_abs] at key
  have h1 : 1 ≤ Real.exp (a * t) := Real.one_le_exp (by positivity)
  have h0 : 0 ≤ |g 0| := abs_nonneg _
  nlinarith

private lemma fc3_integrable (g : ℝ → ℝ) (s : ℂ) (a C : ℝ) (hg : Continuous g)
    (hb : ∀ t, 0 ≤ t → |g t| ≤ C * Real.exp (a * t)) (has : a < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (g t : ℂ)) (Ioi 0) := by
  have hint : IntegrableOn (fun t : ℝ => C * Real.exp (-(s.re - a) * t)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul C
  refine hint.mono' (by fun_prop) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hre : (-s * (t : ℂ)).re = -s.re * t := by simp
  rw [hre]
  calc Real.exp (-s.re * t) * |g t| ≤ Real.exp (-s.re * t) * (C * Real.exp (a * t)) :=
        mul_le_mul_of_nonneg_left (hb t (le_of_lt ht)) (Real.exp_pos _).le
    _ = C * Real.exp (-(s.re - a) * t) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf

private lemma fc3_tendsto (g : ℝ → ℝ) (s : ℂ) (a C : ℝ)
    (hb : ∀ t, 0 ≤ t → |g t| ≤ C * Real.exp (a * t)) (has : a < s.re) :
    Tendsto (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (g t : ℂ)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => C * Real.exp (-(s.re - a) * t)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun t : ℝ => Real.exp (-((s.re - a) * t))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (show 0 < s.re - a by linarith))
    convert h2.const_mul C using 1
    · funext t; ring_nf
    · simp
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hre : (-s * (t : ℂ)).re = -s.re * t := by simp
  rw [hre]
  calc Real.exp (-s.re * t) * |g t| ≤ Real.exp (-s.re * t) * (C * Real.exp (a * t)) :=
        mul_le_mul_of_nonneg_left (hb t ht) (Real.exp_pos _).le
    _ = C * Real.exp (-(s.re - a) * t) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf
private lemma fc3_laplace_deriv (g g' : ℝ → ℝ) (s : ℂ) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hgi : IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (g t : ℂ)) (Ioi 0))
    (hg'i : IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (g' t : ℂ)) (Ioi 0))
    (hlim : Tendsto (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (g t : ℂ)) atTop (𝓝 0)) :
    laplace g' s = s * laplace g s - (g 0 : ℂ) := by
  unfold laplace
  have hu : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun t : ℝ => Complex.exp (-s * (t : ℂ)))
      (-s * Complex.exp (-s * (x : ℂ))) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => -s * (t : ℂ)) (-s * 1) x :=
      (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-s) |>.congr_deriv (by simp)
    have := h1.cexp
    convert this using 1; ring
  have hv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun t : ℝ => (g t : ℂ)) ((g' x : ℝ) : ℂ) x :=
    fun x _ => (hg x).ofReal_comp
  have hu'v : IntegrableOn ((fun x : ℝ => -s * Complex.exp (-s * (x : ℂ))) * fun t : ℝ => (g t : ℂ)) (Ioi 0) := by
    have := hgi.const_mul (-s)
    refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply]; ring
  have hzero : Tendsto ((fun t : ℝ => Complex.exp (-s * (t : ℂ))) * fun t : ℝ => (g t : ℂ))
      (𝓝[>] 0) (𝓝 (Complex.exp (-s * ((0:ℝ) : ℂ)) * (g 0 : ℂ))) := by
    have hc : Continuous ((fun t : ℝ => Complex.exp (-s * (t : ℂ))) * fun t : ℝ => (g t : ℂ)) := by
      have : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
      fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hu hv hg'i hu'v hzero hlim
  rw [key]
  have h2 : ∫ x in Ioi (0:ℝ), -s * Complex.exp (-s * (x : ℂ)) * (g x : ℂ)
      = -s * ∫ x in Ioi (0:ℝ), Complex.exp (-s * (x : ℂ)) * (g x : ℂ) := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  rw [h2]; simp; ring

theorem solution (ν α : ℝ) (f : ℝ → ℝ) (s : ℂ)
    (hν : 0 < ν) (n : ℕ) (hn : n = Nat.ceil ν)
    (hsmooth : ContDiff ℝ n f)
    (hexp : ∃ M T : ℝ, 0 < M ∧ 0 < T ∧ ∀ t ≥ T, |f t| ≤ M * Real.exp (α * t))
    (hexpn : ∃ M T : ℝ, 0 < M ∧ 0 < T ∧ ∀ t ≥ T, |iteratedDeriv n f t| ≤ M * Real.exp (α * t))
    (hsα : α < s.re) (hs0 : 0 < s.re) :
    laplace (caputoDeriv 0 ν f) s =
      s ^ (ν : ℂ) * laplace f s -
        Finset.sum (Finset.range n) (fun k => s ^ (ν - k - 1 : ℂ) * Complex.ofReal (iteratedDeriv k f (0 : ℝ))) := by
  have hs : s ≠ 0 := fun h => by simp [h] at hs0
  set a : ℝ := (max α 0 + s.re) / 2 with ha_def
  have hm1 : α ≤ max α 0 := le_max_left _ _
  have hm2 : 0 ≤ max α 0 := le_max_right _ _
  have hm3 : max α 0 < s.re := max_lt hsα hs0
  have ha : 0 < a := by rw [ha_def]; linarith
  have hαa : α < a := by rw [ha_def]; linarith
  have has : a < s.re := by rw [ha_def]; linarith
  have hcont : ∀ k ≤ n, Continuous (iteratedDeriv k f) := fun k hk =>
    hsmooth.continuous_iteratedDeriv k (by exact_mod_cast hk)
  have hderiv : ∀ k < n, ∀ t, HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f t) t := by
    intro k hk t
    have := (hsmooth.differentiable_iteratedDeriv k (by exact_mod_cast hk)) t
    rw [iteratedDeriv_succ]; exact this.hasDerivAt
  have hbn : ∃ C, ∀ t, 0 ≤ t → |iteratedDeriv n f t| ≤ C * Real.exp (a * t) := by
    obtain ⟨M, T, hM, hT, hb⟩ := hexpn
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn
      (hcont n le_rfl).continuousOn
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hT.le⟩)
    refine ⟨M + B, fun t ht => ?_⟩
    have he1 : 1 ≤ Real.exp (a * t) := Real.one_le_exp (by positivity)
    by_cases htT : T ≤ t
    · have h1 := hb t htT
      have h2 : Real.exp (α * t) ≤ Real.exp (a * t) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hαa.le ht)
      have h3 : M * Real.exp (α * t) ≤ M * Real.exp (a * t) := mul_le_mul_of_nonneg_left h2 hM.le
      nlinarith
    · have h1 := hB t ⟨ht, le_of_lt (not_le.1 htT)⟩
      rw [Real.norm_eq_abs] at h1
      nlinarith
  have hbk : ∀ j ≤ n, ∃ C, ∀ t, 0 ≤ t → |iteratedDeriv (n - j) f t| ≤ C * Real.exp (a * t) := by
    intro j
    induction j with
    | zero => intro _; simpa using hbn
    | succ j ih =>
      intro hj
      obtain ⟨C, hC⟩ := ih (by omega)
      have hk : n - (j + 1) + 1 = n - j := by omega
      exact ⟨_, fc3_bound_of_deriv (iteratedDeriv (n - (j + 1)) f) (iteratedDeriv (n - (j + 1) + 1) f)
        a C ha (hderiv _ (by omega)) (by rw [hk]; exact hC)⟩
  have hbk' : ∀ k ≤ n, ∃ C, ∀ t, 0 ≤ t → |iteratedDeriv k f t| ≤ C * Real.exp (a * t) := by
    intro k hk
    have := hbk (n - k) (by omega)
    rwa [show n - (n - k) = k by omega] at this
  have hL : ∀ k ≤ n, laplace (iteratedDeriv k f) s =
      s ^ k * laplace f s - ∑ j ∈ Finset.range k, s ^ (k - 1 - j) * ((iteratedDeriv j f 0 : ℝ) : ℂ) := by
    intro k
    induction k with
    | zero => intro _; simp [iteratedDeriv_zero]
    | succ k ih =>
      intro hk
      obtain ⟨C, hC⟩ := hbk' k (by omega)
      obtain ⟨C', hC'⟩ := hbk' (k + 1) hk
      rw [fc3_laplace_deriv (iteratedDeriv k f) (iteratedDeriv (k + 1) f) s (hderiv k (by omega))
        (fc3_integrable _ s a C (hcont k (by omega)) hC has)
        (fc3_integrable _ s a C' (hcont _ hk) hC' has) (fc3_tendsto _ s a C hC has), ih (by omega)]
      rw [Finset.sum_range_succ, mul_sub, Finset.mul_sum, pow_succ]
      have : ∀ j ∈ Finset.range k, s * (s ^ (k - 1 - j) * ((iteratedDeriv j f 0 : ℝ) : ℂ))
          = s ^ (k + 1 - 1 - j) * ((iteratedDeriv j f 0 : ℝ) : ℂ) := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [show k + 1 - 1 - j = (k - 1 - j) + 1 by omega, pow_succ]; ring
      rw [Finset.sum_congr rfl this, show k + 1 - 1 - k = 0 by omega]
      ring
  have hcap : caputoDeriv 0 ν f = rlIntegral 0 ((n : ℝ) - ν) (iteratedDeriv n f) := by
    funext x; rw [hn]; rfl
  have hnν : ν ≤ n := hn ▸ Nat.le_ceil ν
  have hexpo : ∀ j ∈ Finset.range n, ((n - 1 - j : ℕ) : ℂ) = (n : ℂ) - j - 1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Nat.cast_sub (by omega : j ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast; ring
  rw [hcap]
  by_cases hμ : (n : ℝ) - ν = 0
  · have hrl : rlIntegral 0 ((n : ℝ) - ν) (iteratedDeriv n f) = iteratedDeriv n f := by
      funext x; simp [rlIntegral, hμ]
    have hνn : ν = n := by linarith
    rw [hrl, hL n le_rfl, hνn, Complex.ofReal_natCast, Complex.cpow_natCast]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Complex.cpow_natCast, hexpo j hj]
  · have hμpos : 0 < (n : ℝ) - ν := lt_of_le_of_ne (by linarith) (Ne.symm hμ)
    rw [laplace_rlIntegral ((n : ℝ) - ν) α (iteratedDeriv n f) s hμpos (hcont n le_rfl).continuousOn
      hexpn hsα hs0, hL n le_rfl, sub_div, Finset.sum_div]
    congr 1
    · rw [mul_div_right_comm, ← Complex.cpow_natCast, ← Complex.cpow_sub _ _ hs]
      congr 2; push_cast; ring
    · apply Finset.sum_congr rfl
      intro j hj
      rw [mul_div_right_comm, ← Complex.cpow_natCast, ← Complex.cpow_sub _ _ hs, hexpo j hj]
      congr 2; push_cast; ring
