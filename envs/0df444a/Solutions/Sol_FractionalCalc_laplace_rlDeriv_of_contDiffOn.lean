-- Prove2me | solution 1 for FractionalCalc.laplace_rlDeriv_of_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T07:54:28.652909+00:00
-- url     : https://prove2.me/submissions/d22a93b6-8d55-4eaf-9005-1180e07ba1d7

import Mathlib
import Definitions.Def_FractionalCalc_rlIntegral
import Definitions.Def_FractionalCalc_rlDeriv
import Definitions.Def_QueueingFundamentals_Transient_laplace
import Theorems.Thm_FractionalCalc_laplace_rlIntegral
open MeasureTheory Set Classical QueueingFundamentals.Transient Filter
open FractionalCalc
set_option autoImplicit false
private lemma fc4_ibp (h h' : ℝ → ℝ) (ℓ : ℝ) (s : ℂ)
    (hd : ∀ t ∈ Ioi (0:ℝ), HasDerivAt h (h' t) t)
    (hlim : Tendsto h (nhdsWithin 0 (Ioi 0)) (nhds ℓ))
    (hi : IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * (h t : ℂ)) (Ioi 0))
    (hi' : IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * (h' t : ℂ)) (Ioi 0))
    (htop : Tendsto (fun t : ℝ => Complex.exp (-s * t) * (h t : ℂ)) atTop (nhds 0)) :
    laplace h' s = s * laplace h s - ℓ := by
  unfold laplace
  have hu : ∀ t ∈ Ioi (0:ℝ), HasDerivAt (fun t : ℝ => Complex.exp (-s * t))
      (-s * Complex.exp (-s * t)) t := by
    intro t _
    have h1 : HasDerivAt (fun x : ℂ => Complex.exp (-s * x)) (Complex.exp (-s * t) * (-s)) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).const_mul (-s)).cexp
    simpa [mul_comm] using h1.comp_ofReal
  have key := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := (ℓ:ℂ)) (b' := 0)
    (u := fun t : ℝ => Complex.exp (-s * t)) (v := fun t => (h t : ℂ))
    (u' := fun t : ℝ => -s * Complex.exp (-s * t)) (v' := fun t => (h' t : ℂ)) hu
    (fun t ht => (hd t ht).ofReal_comp) hi' ?_ ?_ htop
  · rw [key]
    have : ∫ x in Ioi (0:ℝ), -s * Complex.exp (-s * x) * (h x : ℂ)
        = -s * ∫ x in Ioi (0:ℝ), Complex.exp (-s * x) * (h x : ℂ) := by
      simp_rw [mul_assoc]; exact integral_const_mul _ _
    rw [this]; ring
  · have : (fun t : ℝ => -s * Complex.exp (-s * t)) * (fun t => (h t : ℂ))
        = fun t : ℝ => -s * (Complex.exp (-s * t) * (h t : ℂ)) := by
      funext t; simp [mul_assoc]
    rw [this]; exact hi.const_mul _
  · have h1 : Tendsto (fun t : ℝ => Complex.exp (-s * t)) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
      have : Continuous (fun t : ℝ => Complex.exp (-s * t)) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t => (h t : ℂ)) (nhdsWithin 0 (Ioi 0)) (nhds (ℓ:ℂ)) :=
      (Complex.continuous_ofReal.tendsto ℓ).comp hlim
    have := h1.mul h2
    rw [one_mul] at this
    exact this

private lemma fc4_norm_exp (s : ℂ) (t : ℝ) :
    ‖Complex.exp (-s * t)‖ = Real.exp (-(s.re * t)) := by
  rw [Complex.norm_exp]; simp

private lemma fc4_lapInt (φ : ℝ → ℝ) (s : ℂ) (b T M : ℝ) (hT : 0 < T)
    (hc : ContinuousOn φ (Ioi 0)) (hloc : IntegrableOn φ (Ioc 0 T))
    (hb : ∀ t ≥ T, |φ t| ≤ M * Real.exp (b * t)) (hbs : b < s.re) (hs0 : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * t) * (φ t : ℂ)) (Ioi 0) := by
  have hcF : ContinuousOn (fun t : ℝ => Complex.exp (-s * t) * (φ t : ℂ)) (Ioi 0) := by
    apply ContinuousOn.mul
    · exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-s * t))).continuousOn
    · exact Complex.continuous_ofReal.comp_continuousOn hc
  rw [← Ioc_union_Ioi_eq_Ioi hT.le]
  apply IntegrableOn.union
  · refine Integrable.mono' hloc.norm ((hcF.mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, fc4_norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have : Real.exp (-(s.re * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [ht.1]
    nlinarith [abs_nonneg (φ t), Real.exp_pos (-(s.re * t))]
  · have hg : IntegrableOn (fun t : ℝ => M * Real.exp (-(s.re - b) * t)) (Ioi T) :=
      (exp_neg_integrableOn_Ioi T (sub_pos.2 hbs)).const_mul M
    refine Integrable.mono' hg ((hcF.mono (Ioi_subset_Ioi hT.le)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, fc4_norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hb t (le_of_lt ht)
    calc Real.exp (-(s.re * t)) * |φ t| ≤ Real.exp (-(s.re * t)) * (M * Real.exp (b * t)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = M * Real.exp (-(s.re - b) * t) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

private lemma fc4_intExp (a M x y : ℝ) (ha : 0 < a) :
    ∫ u in x..y, M * Real.exp (a * u) = M / a * Real.exp (a * y) - M / a * Real.exp (a * x) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u _
    have := ((hasDerivAt_id u).const_mul a).exp.const_mul (M / a)
    simp only [id, mul_one] at this
    have e : M * Real.exp (a * u) = M / a * (Real.exp (a * u) * a) := by
      field_simp
    rw [e]; exact this
  · exact (by fun_prop : Continuous (fun u : ℝ => M * Real.exp (a * u))).intervalIntegrable _ _

private lemma fc4_E (φ : ℝ → ℝ) (a T M : ℝ) (ha : 0 < a) (hT : 0 < T)
    (hint : ∀ t > 0, IntervalIntegrable φ volume 0 t)
    (hb : ∀ t ≥ T, |φ t| ≤ M * Real.exp (a * t)) :
    ∃ C, ∀ t > 0, ∫ x in (0:ℝ)..t, |φ x| ≤ C * Real.exp (a * t) := by
  have hM : 0 ≤ M := by
    have := hb T le_rfl
    have h0 := abs_nonneg (φ T)
    by_contra hneg
    push Not at hneg
    nlinarith [Real.exp_pos (a * T)]
  set I := ∫ x in (0:ℝ)..T, |φ x|
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg hT.le (fun x _ => abs_nonneg _)
  refine ⟨I + M / a, fun t ht => ?_⟩
  have he : 1 ≤ Real.exp (a * t) := Real.one_le_exp (by positivity)
  have hMa : 0 ≤ M / a := div_nonneg hM ha.le
  rcases le_or_gt t T with htT | htT
  · have h1 : ∫ x in (0:ℝ)..t, |φ x| ≤ I :=
      intervalIntegral.integral_mono_interval le_rfl ht.le htT
        (Eventually.of_forall fun x => abs_nonneg _) (hint T hT).abs
    nlinarith
  · have hTt : IntervalIntegrable (fun x => |φ x|) volume T t := by
      refine ((hint t ht).abs).mono_set ?_
      rw [uIcc_of_le (le_of_lt htT), uIcc_of_le ht.le]
      exact Icc_subset_Icc_left hT.le
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint T hT).abs hTt]
    have h2 : ∫ x in T..t, |φ x| ≤ ∫ x in T..t, M * Real.exp (a * x) :=
      intervalIntegral.integral_mono_on (le_of_lt htT) hTt
        ((by fun_prop : Continuous (fun u : ℝ => M * Real.exp (a * u))).intervalIntegrable _ _)
        (fun x hx => hb x hx.1)
    rw [fc4_intExp a M T t ha] at h2
    have : 0 ≤ M / a * Real.exp (a * T) := by positivity
    nlinarith

private lemma fc4_B (ψ φ : ℝ → ℝ) (ℓ a C : ℝ) (ha : 0 < a)
    (hd : ∀ t ∈ Ioi (0:ℝ), HasDerivAt ψ (φ t) t)
    (hlim : Tendsto ψ (nhdsWithin 0 (Ioi 0)) (nhds ℓ))
    (hint : ∀ t > 0, IntervalIntegrable φ volume 0 t)
    (hE : ∀ t > 0, ∫ x in (0:ℝ)..t, |φ x| ≤ C * Real.exp (a * t)) :
    ∀ t > 0, |ψ t| ≤ (|ℓ| + C) * Real.exp (a * t) := by
  intro t ht
  have hF : ∫ x in (0:ℝ)..t, φ x = ψ t - ℓ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto ht (fun x hx => hd x hx.1)
      (hint t ht) hlim ((hd t ht).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have h1 := intervalIntegral.abs_integral_le_integral_abs (f := φ) (μ := volume) ht.le
  rw [hF] at h1
  have h2 := hE t ht
  have he : 1 ≤ Real.exp (a * t) := Real.one_le_exp (by positivity)
  have h3 : |ψ t| ≤ |ℓ| + |ψ t - ℓ| := by
    have := abs_add_le ℓ (ψ t - ℓ); simpa using this
  nlinarith [abs_nonneg ℓ]

private lemma fc4_intInt (ψ : ℝ → ℝ) (a D : ℝ) (ha : 0 < a) (hc : ContinuousOn ψ (Ioi 0))
    (hB : ∀ t > 0, |ψ t| ≤ D * Real.exp (a * t)) :
    ∀ t > 0, IntervalIntegrable ψ volume 0 t := by
  intro t ht
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  have hD : 0 ≤ D := by
    have := hB 1 one_pos
    have h0 := abs_nonneg (ψ 1)
    by_contra hneg
    push Not at hneg
    nlinarith [Real.exp_pos (a * 1)]
  refine Integrable.mono' (g := fun _ => D * Real.exp (a * t)) (integrableOn_const ?_)
    ((hc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
  · simp
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs]
    calc |ψ x| ≤ D * Real.exp (a * x) := hB x hx.1
      _ ≤ D * Real.exp (a * t) := by
        apply mul_le_mul_of_nonneg_left _ hD
        exact Real.exp_le_exp.2 (by nlinarith [hx.2])

theorem solution (ν α : ℝ) (f : ℝ → ℝ) (s : ℂ)
    (hν : 0 < ν) (n : ℕ) (hn : n = Nat.floor ν + 1)
    (hf : ContinuousOn f (Ici 0))
    (hexp : ∃ M T : ℝ, 0 < M ∧ 0 < T ∧ ∀ t ≥ T, |f t| ≤ M * Real.exp (α * t))
    (hg : ContDiffOn ℝ n (rlIntegral 0 ((n : ℝ) - ν) f) (Ioi 0))
    (hloc : ∀ T : ℝ, 0 < T → IntegrableOn (rlDeriv 0 ν f) (Ioc 0 T))
    (L : ℕ → ℝ)
    (hL : ∀ k ∈ Finset.range n,
      Tendsto (iteratedDeriv k (rlIntegral 0 ((n : ℝ) - ν) f)) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (L k)))
    (hexpn : ∃ M T : ℝ, 0 < M ∧ 0 < T ∧ ∀ t ≥ T, |rlDeriv 0 ν f t| ≤ M * Real.exp (α * t))
    (hsα : α < s.re) (hs0 : 0 < s.re) :
    laplace (rlDeriv 0 ν f) s =
      s ^ (ν : ℂ) * laplace f s -
        Finset.sum (Finset.range n) (fun k => s ^ (n - k - 1 : ℂ) * (L k : ℂ)) := by
  set g := rlIntegral 0 ((n : ℝ) - ν) f with hgdef
  have hD : rlDeriv 0 ν f = iteratedDeriv n g := by
    funext x; subst hn; rfl
  rw [hD] at hloc hexpn ⊢
  have hs : s ≠ 0 := by
    rintro rfl; simp at hs0
  -- derivatives and continuity
  have hderiv : ∀ k < n, ∀ t ∈ Ioi (0:ℝ),
      HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k+1) g t) t := by
    intro k hk t ht
    have hdo := hg.differentiableOn_iteratedDerivWithin (m := k) (by exact_mod_cast hk)
      isOpen_Ioi.uniqueDiffOn
    have hdo' : DifferentiableOn ℝ (iteratedDeriv k g) (Ioi 0) :=
      hdo.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm)
    rw [iteratedDeriv_succ]
    exact ((hdo' t ht).differentiableAt (isOpen_Ioi.mem_nhds ht)).hasDerivAt
  have hcont : ∀ k ≤ n, ContinuousOn (iteratedDeriv k g) (Ioi 0) := by
    intro k hk
    have hco := hg.continuousOn_iteratedDerivWithin (m := k) (by exact_mod_cast hk)
      isOpen_Ioi.uniqueDiffOn
    exact hco.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioi hx).symm)
  -- exponent a
  set a := (max α 0 + s.re) / 2 with hadef
  have ha0 : 0 < a := by
    have := le_max_right α 0; rw [hadef]; linarith
  have hαa : α ≤ a := by
    have := le_max_left α 0; have := le_max_right α 0
    have : max α 0 < s.re := max_lt hsα hs0
    rw [hadef]; linarith
  have has : a < s.re := by
    have : max α 0 < s.re := max_lt hsα hs0
    rw [hadef]; linarith
  obtain ⟨Mn, Tn, hMn, hTn, hbn⟩ := hexpn
  have hintn : ∀ t > 0, IntervalIntegrable (iteratedDeriv n g) volume 0 t := fun t ht =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).2 (hloc t ht)
  have hEn : ∃ C, ∀ t > 0, ∫ x in (0:ℝ)..t, |iteratedDeriv n g x| ≤ C * Real.exp (a * t) := by
    refine fc4_E _ a Tn Mn ha0 hTn hintn (fun t ht => (hbn t ht).trans ?_)
    apply mul_le_mul_of_nonneg_left _ hMn.le
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hαa (hTn.le.trans ht))
  -- bounds for k < n
  have hB : ∀ j k, k + j + 1 = n → ∃ D, ∀ t > 0, |iteratedDeriv k g t| ≤ D * Real.exp (a * t) := by
    intro j
    induction j with
    | zero =>
      intro k hk
      have hk' : k + 1 = n := by omega
      obtain ⟨C, hC⟩ := hEn
      subst hk'
      exact ⟨_, fc4_B _ _ (L k) a C ha0 (hderiv k (by omega)) (hL k (Finset.mem_range.2 (by omega)))
        hintn hC⟩
    | succ j ih =>
      intro k hk
      obtain ⟨D, hDb⟩ := ih (k+1) (by omega)
      have hi := fc4_intInt _ a D ha0 (hcont (k+1) (by omega)) hDb
      obtain ⟨C, hC⟩ := fc4_E _ a 1 D ha0 one_pos hi (fun t ht => hDb t (by linarith))
      exact ⟨_, fc4_B _ _ (L k) a C ha0 (hderiv k (by omega)) (hL k (Finset.mem_range.2 (by omega)))
        hi hC⟩
  have hB' : ∀ k < n, ∃ D, ∀ t > 0, |iteratedDeriv k g t| ≤ D * Real.exp (a * t) :=
    fun k hk => hB (n - k - 1) k (by omega)
  -- Laplace integrability
  have hI : ∀ k ≤ n, IntegrableOn
      (fun t : ℝ => Complex.exp (-s * t) * ((iteratedDeriv k g t : ℝ) : ℂ)) (Ioi 0) := by
    intro k hk
    rcases lt_or_eq_of_le hk with hk | rfl
    · obtain ⟨D, hDb⟩ := hB' k hk
      have hi := fc4_intInt _ a D ha0 (hcont k hk.le) hDb
      exact fc4_lapInt _ s a 1 D one_pos (hcont k hk.le)
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 (hi 1 one_pos))
        (fun t ht => hDb t (by linarith)) has hs0
    · exact fc4_lapInt _ s α Tn Mn hTn (hcont _ le_rfl) (hloc Tn hTn) hbn hsα hs0
  have htop : ∀ k < n, Tendsto
      (fun t : ℝ => Complex.exp (-s * t) * ((iteratedDeriv k g t : ℝ) : ℂ)) atTop (nhds 0) := by
    intro k hk
    obtain ⟨D, hDb⟩ := hB' k hk
    have hlim : Tendsto (fun t : ℝ => D * Real.exp (-(s.re - a) * t)) atTop (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ => -(s.re - a) * t) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith)
      simpa using (Real.tendsto_exp_atBot.comp h1).const_mul D
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_mul, fc4_norm_exp, Complex.norm_real, Real.norm_eq_abs]
    calc Real.exp (-(s.re * t)) * |iteratedDeriv k g t|
        ≤ Real.exp (-(s.re * t)) * (D * Real.exp (a * t)) :=
          mul_le_mul_of_nonneg_left (hDb t ht) (Real.exp_pos _).le
      _ = D * Real.exp (-(s.re - a) * t) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hstep : ∀ k < n, laplace (iteratedDeriv (k+1) g) s
      = s * laplace (iteratedDeriv k g) s - L k := fun k hk =>
    fc4_ibp _ _ (L k) s (hderiv k hk) (hL k (Finset.mem_range.2 hk)) (hI k hk.le)
      (hI (k+1) hk) (htop k hk)
  have hind : ∀ k ≤ n, laplace (iteratedDeriv k g) s = s ^ k * laplace g s -
      Finset.sum (Finset.range k) (fun j => s ^ ((k:ℂ) - j - 1) * (L j : ℂ)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [hstep k (by omega), ih (by omega), Finset.sum_range_succ, mul_sub, Finset.mul_sum]
      have e1 : ∀ j ∈ Finset.range k, s * (s ^ ((k:ℂ) - j - 1) * (L j : ℂ))
          = s ^ (((k+1 : ℕ) : ℂ) - j - 1) * (L j : ℂ) := by
        intro j _
        have : ((k+1 : ℕ) : ℂ) - j - 1 = ((k:ℂ) - j - 1) + 1 := by push_cast; ring
        rw [this, Complex.cpow_add _ _ hs, Complex.cpow_one]; ring
      rw [Finset.sum_congr rfl e1]
      have e2 : ((k+1 : ℕ) : ℂ) - (k:ℂ) - 1 = 0 := by push_cast; ring
      rw [e2, Complex.cpow_zero, pow_succ]; ring
  rw [hind n le_rfl]
  have hμ : 0 < (n : ℝ) - ν := by
    rw [hn]; push_cast; linarith [Nat.lt_floor_add_one ν]
  rw [laplace_rlIntegral ((n:ℝ) - ν) α f s hμ hf hexp hsα hs0]
  congr 1
  have hsμ : s ^ (((n:ℝ) - ν : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hs]; exact Complex.exp_ne_zero _
  have hsn : s ^ n = s ^ (ν : ℂ) * s ^ (((n:ℝ) - ν : ℝ) : ℂ) := by
    rw [← Complex.cpow_add _ _ hs, ← Complex.cpow_natCast]; congr 1; push_cast; ring
  rw [hsn]; field_simp
