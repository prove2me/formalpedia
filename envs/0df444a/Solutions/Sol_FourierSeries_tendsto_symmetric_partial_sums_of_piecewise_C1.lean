-- Prove2me | solution 1 for FourierSeries.tendsto_symmetric_partial_sums_of_piecewise_C1
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:49:46.008276+00:00
-- url     : https://prove2.me/submissions/34dcc055-5370-4c16-9d41-4d8b96e21ad6

import Mathlib

open Filter Topology
open scoped Real ContDiff

set_option autoImplicit false

namespace Sol_FourierSeries_tendsto_symmetric_partial_sums_of_piecewise_C1

open MeasureTheory Set
open scoped FourierTransform

local notation "twoPiI" => (2 * (Real.pi : ℂ) * Complex.I)

/-- Multiplying the Dirichlet kernel by one exponential difference telescopes. -/
private theorem sum_exp_int_mul_sub_one (N : ℕ) (x : ℝ) :
    (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), Complex.exp (twoPiI * m * (x : ℂ))) *
      (Complex.exp (twoPiI * (x : ℂ)) - 1) =
    Complex.exp (twoPiI * (N + 1 : ℕ) * (x : ℂ)) -
      Complex.exp (twoPiI * (-(N : ℤ)) * (x : ℂ)) := by
  let e (m : ℤ) := Complex.exp (twoPiI * m * (x : ℂ))
  have he (m : ℤ) :
      e m * (Complex.exp (twoPiI * (x : ℂ)) - 1) = e (m + 1) - e m := by
    simp only [mul_sub, mul_one, e, ← Complex.exp_add, Int.cast_add, Int.cast_one]
    congr 2
    ring
  rw [Finset.sum_mul]
  change (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), e m * _) = _
  simp_rw [he]
  have hsum :
      ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (e (m + 1) - e m) =
        ∑ i ∈ Finset.range (2 * N + 1), (e ((i : ℤ) - N + 1) - e ((i : ℤ) - N)) := by
    symm
    apply Finset.sum_bij (fun (i : ℕ) _ ↦ (i : ℤ) - N)
    · intro i hi
      simp only [Finset.mem_range, Finset.mem_Icc] at hi ⊢
      omega
    · intro i _ j _ hij
      omega
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      refine ⟨(m + N).toNat, Finset.mem_range.mpr (by omega), by omega⟩
    · intro i _
      rfl
  rw [hsum]
  let E (i : ℕ) := e ((i : ℤ) - N)
  have hstep (i : ℕ) : (i : ℤ) - N + 1 = ((i + 1 : ℕ) : ℤ) - N := by omega
  simp_rw [hstep]
  change (∑ i ∈ Finset.range (2 * N + 1), (E (i + 1) - E i)) = _
  rw [Finset.sum_range_sub]
  have hlast : ((2 * N + 1 : ℕ) : ℤ) - N = (N : ℤ) + 1 := by omega
  change e ((↑(2 * N + 1) : ℤ) - ↑N) - e ((0 : ℤ) - ↑N) = _
  rw [hlast, zero_sub]
  simp [e]

private theorem fourier_indicator_eq_integral_exp (Q : ℝ → ℂ) (b w : ℝ) :
    𝓕 ((Ioc 0 b).indicator Q) w =
      ∫ x in Ioc 0 b, Complex.exp (twoPiI * (-(w : ℂ)) * (x : ℂ)) * Q x := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ioc 0 b
  · simp only [indicator_of_mem hx, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    congr 2
    ring
  · simp [hx]

/-- A Riemann–Lebesgue argument for symmetric Fourier sums at a jump. The quotient
hypothesis measures how fast the even part approaches its limiting value at zero. -/
theorem tendsto_symmetric_fourier_integrals_of_integrable_quotient
    {F : ℝ → ℂ} (hF : IntervalIntegrable F volume (-(1 / 2)) (1 / 2)) {L : ℂ}
    (hquot : IntegrableOn
      (fun x : ℝ ↦ (F x + F (-x) - 2 * L) / (Complex.exp (twoPiI * (x : ℂ)) - 1))
      (Ioc 0 (1 / 2))) :
    Tendsto (fun N : ℕ ↦ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), Complex.exp (twoPiI * (m : ℂ) * (x : ℂ)) * F x)
      atTop (𝓝 L) := by
  let b : ℝ := 1 / 2
  have hb : 0 ≤ b := by norm_num [b]
  let e (m : ℤ) (x : ℝ) := Complex.exp (twoPiI * (m : ℂ) * (x : ℂ))
  let D (N : ℕ) (x : ℝ) := ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), e m x
  have he (m : ℤ) : Continuous (e m) := by dsimp [e]; fun_prop
  have hD (N : ℕ) : Continuous (D N) := continuous_finsetSum _ fun m _ ↦ he m
  have hDeven (N : ℕ) (x : ℝ) : D N (-x) = D N x := by
    unfold D
    apply Finset.sum_bij (fun m _ ↦ -m)
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro m _ n _ h
      omega
    · intro m hm
      simp only [Finset.mem_Icc] at hm
      exact ⟨-m, Finset.mem_Icc.mpr (by omega), by simp⟩
    · intro m _
      simp [e]
  have hmass (N : ℕ) : (∫ x in -b..b, D N x) = 1 := by
    rw [show (fun x ↦ D N x) = fun x ↦ ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), e m x from rfl,
      intervalIntegral.integral_finsetSum (fun m _ ↦ (he m).intervalIntegrable _ _)]
    have heint (m : ℤ) (hm : m ≠ 0) : (∫ x in -b..b, e m x) = 0 := by
      have hconst : twoPiI * (m : ℂ) ≠ 0 := by
        have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
        exact mul_ne_zero
          (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            Complex.I_ne_zero) hm'
      rw [show (fun x ↦ e m x) = _ from rfl, integral_exp_mul_complex hconst]
      have hends : e m b = e m (-b) := by
        have hperiod := Complex.exp_int_mul_two_pi_mul_I m
        have harg : twoPiI * (m : ℂ) * (b : ℂ) =
            twoPiI * (m : ℂ) * ((-b : ℝ) : ℂ) + (m : ℂ) * twoPiI := by
          simp [b]
          ring
        simp only [e, harg, Complex.exp_add, hperiod, mul_one]
      change (e m b - e m (-b)) / _ = _
      rw [hends, sub_self, zero_div]
    rw [Finset.sum_eq_single 0 (fun m _ hm ↦ heint m hm)]
    · norm_num [e, b, intervalIntegral.integral_const, smul_eq_mul]
    · simp
  let Q (x : ℝ) := (F x + F (-x) - 2 * L) / (Complex.exp (twoPiI * (x : ℂ)) - 1)
  have hnonzero (x : ℝ) (hx : x ∈ Ioc 0 b) : Complex.exp (twoPiI * (x : ℂ)) - 1 ≠ 0 := by
    have hx' : 0 < Real.pi * x := mul_pos Real.pi_pos hx.1
    have hx'' : Real.pi * x < Real.pi := by
      have : x < 1 := hx.2.trans_lt (by norm_num [b])
      nlinarith [mul_pos Real.pi_pos (sub_pos.mpr this)]
    have heq : twoPiI * (x : ℂ) = Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [← norm_ne_zero_iff, heq, Complex.norm_exp_I_mul_ofReal_sub_one]
    have hs : 0 < Real.sin (2 * Real.pi * x / 2) := by
      rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring]
      exact Real.sin_pos_of_pos_of_lt_pi hx' hx''
    exact norm_ne_zero_iff.mpr (mul_ne_zero two_ne_zero hs.ne')
  have hfold (H : ℝ → ℂ) (hH : IntervalIntegrable H volume (-b) b) (N : ℕ) :
      (∫ x in -b..b, D N x * H x) =
        ∫ x in (0 : ℝ)..b, D N x * (H x + H (-x)) := by
    have hi : IntervalIntegrable (fun x ↦ D N x * H x) volume (-b) b := by
      simpa only [mul_comm] using hH.mul_continuousOn (hD N).continuousOn
    have hleft : IntervalIntegrable (fun x ↦ D N x * H x) volume (-b) 0 := by
      apply hi.mono_set
      rw [uIcc_of_le (neg_nonpos.mpr hb), uIcc_of_le (by linarith : -b ≤ b)]
      exact Icc_subset_Icc_right hb
    have hright : IntervalIntegrable (fun x ↦ D N x * H x) volume 0 b := by
      apply hi.mono_set
      rw [uIcc_of_le hb, uIcc_of_le (by linarith : -b ≤ b)]
      exact Icc_subset_Icc_left (neg_nonpos.mpr hb)
    have hreflect : IntervalIntegrable (fun x ↦ D N x * H (-x)) volume 0 b := by
      have := (IntervalIntegrable.iff_comp_neg).mp hleft
      simpa only [hDeven, neg_neg, neg_zero] using this.symm
    have hneg : (∫ x in (0 : ℝ)..b, D N x * H (-x)) = ∫ x in -b..0, D N x * H x := by
      simpa only [hDeven, neg_zero] using
        (intervalIntegral.integral_comp_neg (f := fun x ↦ D N x * H x) (a := 0) (b := b))
    simp_rw [mul_add]
    rw [intervalIntegral.integral_add hright hreflect, hneg, add_comm,
      intervalIntegral.integral_add_adjacent_intervals hleft hright]
  let q := (Ioc 0 b).indicator Q
  have hfreq (N : ℕ) :
      (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ x in -b..b, e m x * F x) - L =
        (𝓕 q (-(N : ℝ) - 1)) - (𝓕 q (N : ℝ)) := by
    have hsum :
        (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∫ x in -b..b, e m x * F x) =
          ∫ x in -b..b, D N x * F x := by
      rw [← intervalIntegral.integral_finsetSum]
      · simp_rw [D, Finset.sum_mul]
      · intro m _
        simpa only [mul_comm] using hF.mul_continuousOn (he m).continuousOn
    have hsub :
        (∫ x in -b..b, D N x * F x) - L = ∫ x in -b..b, D N x * (F x - L) := by
      simp_rw [mul_sub]
      have hprod : IntervalIntegrable (fun x ↦ D N x * F x) volume (-b) b := by
        simpa only [mul_comm] using hF.mul_continuousOn (hD N).continuousOn
      rw [intervalIntegral.integral_sub hprod ((hD N).intervalIntegrable _ _ |>.mul_const L),
        intervalIntegral.integral_mul_const, hmass N, one_mul]
    have hQ : Integrable Q (volume.restrict (Ioc 0 b)) := hquot
    let A (x : ℝ) := Complex.exp (twoPiI * (N + 1 : ℕ) * (x : ℂ))
    let B (x : ℝ) := e (-(N : ℤ)) x
    have hA : Continuous A := by dsimp [A]; fun_prop
    have hB : Continuous B := he _
    have hAnorm (x : ℝ) : ‖A x‖ ≤ 1 := by simp [A, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    have hBnorm (x : ℝ) : ‖B x‖ ≤ 1 := by
      simp [B, e, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
    rw [hsum, hsub, hfold _ (hF.sub intervalIntegrable_const), intervalIntegral.integral_of_le hb]
    calc
      _ = ∫ x in Ioc 0 b, A x * Q x - B x * Q x := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        have hDformula :
            D N x * (Complex.exp (twoPiI * (x : ℂ)) - 1) = A x - B x := by
          simpa only [D, e, A, B, Int.cast_neg, Int.cast_natCast] using
            sum_exp_int_mul_sub_one N x
        change D N x * (F x - L + (F (-x) - L)) = A x * Q x - B x * Q x
        rw [← sub_mul, ← hDformula]
        dsimp only [Q]
        field_simp [hnonzero x hx]
        ring
      _ = (∫ x in Ioc 0 b, A x * Q x) - (∫ x in Ioc 0 b, B x * Q x) :=
        integral_sub (hQ.bdd_mul hA.aestronglyMeasurable (Eventually.of_forall hAnorm))
          (hQ.bdd_mul hB.aestronglyMeasurable (Eventually.of_forall hBnorm))
      _ = _ := by
        change _ = 𝓕 ((Ioc 0 b).indicator Q) (-(N : ℝ) - 1) -
          𝓕 ((Ioc 0 b).indicator Q) (N : ℝ)
        rw [fourier_indicator_eq_integral_exp, fourier_indicator_eq_integral_exp]
        have hAeq (x : ℝ) : A x = Complex.exp
            (twoPiI * (-((-(N : ℝ) - 1 : ℝ) : ℂ)) * (x : ℂ)) := by
          simp [A, Complex.ofReal_sub, add_comm]
        have hBeq (x : ℝ) : B x = Complex.exp
            (twoPiI * (-(N : ℂ)) * (x : ℂ)) := by
          simp [B, e]
        simp_rw [hAeq, hBeq, Complex.ofReal_natCast]
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun n : ℕ ↦ -(n : ℝ) - 1) atTop atBot :=
    (tendsto_atBot_add_const_right _ (-1) (tendsto_neg_atTop_atBot.comp hn)).congr (fun _ ↦ (sub_eq_add_neg ..).symm)
  have hRL := Real.zero_at_infty_fourier q
  have hlim := (hRL.comp (hp.mono_right atBot_le_cocompact)).sub
    (hRL.comp (hn.mono_right atTop_le_cocompact))
  simp only [sub_self] at hlim
  have hadd := (hlim.congr (fun n ↦ (hfreq n).symm)).add_const L
  simpa [e, b] using hadd

/-- A function with one-sided limits at `y` is bounded near `y`. -/
theorem eventually_norm_le_of_one_sided {f : ℝ → ℂ} {y : ℝ} {l r : ℂ}
    (hl : Tendsto f (𝓝[<] y) (𝓝 l)) (hr : Tendsto f (𝓝[>] y) (𝓝 r)) :
    ∀ᶠ t in 𝓝 y, ‖f t‖ ≤ max (max (‖l‖ + 1) (‖r‖ + 1)) ‖f y‖ := by
  have h1 : ∀ᶠ t in 𝓝[<] y, ‖f t‖ < ‖l‖ + 1 :=
    hl.norm.eventually (gt_mem_nhds (lt_add_one _))
  have h2 : ∀ᶠ t in 𝓝[>] y, ‖f t‖ < ‖r‖ + 1 :=
    hr.norm.eventually (gt_mem_nhds (lt_add_one _))
  rw [← nhdsNE_sup_pure, ← nhdsLT_sup_nhdsGT, eventually_sup, eventually_sup, eventually_pure]
  refine ⟨⟨?_, ?_⟩, le_max_right _ _⟩
  · filter_upwards [h1] with t ht
    exact ht.le.trans ((le_max_left _ _).trans (le_max_left _ _))
  · filter_upwards [h2] with t ht
    exact ht.le.trans ((le_max_right _ _).trans (le_max_left _ _))

/-- A function with one-sided limits everywhere is bounded on every compact set. -/
theorem exists_bound_of_one_sided {f : ℝ → ℂ}
    (hlim : ∀ x : ℝ, ∃ l r : ℂ, Tendsto f (𝓝[<] x) (𝓝 l) ∧ Tendsto f (𝓝[>] x) (𝓝 r))
    (K : Set ℝ) (hK : IsCompact K) : ∃ B : ℝ, ∀ t ∈ K, ‖f t‖ ≤ B := by
  refine hK.induction_on (p := fun U => ∃ B : ℝ, ∀ t ∈ U, ‖f t‖ ≤ B) ⟨0, by simp⟩ ?_ ?_ ?_
  · intro U V hUV hV
    obtain ⟨B, hB⟩ := hV
    exact ⟨B, fun t ht => hB t (hUV ht)⟩
  · intro U V hU hV
    obtain ⟨B, hB⟩ := hU
    obtain ⟨B', hB'⟩ := hV
    refine ⟨max B B', fun t ht => ?_⟩
    rcases ht with ht | ht
    · exact (hB t ht).trans (le_max_left _ _)
    · exact (hB' t ht).trans (le_max_right _ _)
  · intro y _
    obtain ⟨l, r, hl, hr⟩ := hlim y
    exact ⟨_, mem_nhdsWithin_of_mem_nhds (eventually_norm_le_of_one_sided hl hr),
      _, fun t ht => ht⟩

/-- A periodic function with one-sided limits everywhere is bounded. -/
theorem exists_global_bound {T : ℝ} (hT : 0 < T) {f : ℝ → ℂ} (hper : Function.Periodic f T)
    (hlim : ∀ x : ℝ, ∃ l r : ℂ, Tendsto f (𝓝[<] x) (𝓝 l) ∧ Tendsto f (𝓝[>] x) (𝓝 r)) :
    ∃ B : ℝ, ∀ t, ‖f t‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_bound_of_one_sided hlim (Icc 0 T) isCompact_Icc
  refine ⟨B, fun t => ?_⟩
  obtain ⟨y, hy, hfy⟩ := hper.exists_mem_Ico₀ hT t
  rw [hfy]
  exact hB y (Ico_subset_Icc_self hy)

/-- A function continuous off a countable set is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_of_continuousAt_off_countable {g : ℝ → ℂ} {C : Set ℝ}
    (hC : C.Countable) (hg : ∀ y ∉ C, ContinuousAt g y) :
    AEStronglyMeasurable g volume := by
  have hcont : ContinuousOn g Cᶜ := fun y hy => (hg y hy).continuousWithinAt
  have h := hcont.aestronglyMeasurable (μ := volume) hC.measurableSet.compl
  have hae : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Cᶜ := by
    rw [ae_iff]
    simpa using hC.measure_zero volume
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h

/-- Points slightly to the right of `x` avoid `S + T ℤ`. -/
theorem eventually_nhdsGT_not_mem {T : ℝ} (hT : 0 < T) (S : Finset ℝ) (x : ℝ) :
    ∀ᶠ t in 𝓝[>] x, ∀ n : ℤ, t + n * T ∉ S := by
  have key : ∀ s ∈ S, ∀ᶠ t in 𝓝[>] x, ∀ n : ℤ, t + n * T ≠ s := by
    intro s _
    have hc : toIocMod hT x s ∈ Ioc x (x + T) := toIocMod_mem_Ioc hT x s
    filter_upwards [Ioo_mem_nhdsGT hc.1] with t ht n htn
    have h : toIocMod hT x s = t := by
      rw [toIocMod_eq_iff]
      refine ⟨⟨ht.1, ht.2.le.trans hc.2⟩, n, ?_⟩
      rw [← htn, zsmul_eq_mul]
    exact absurd h (ne_of_gt ht.2)
  filter_upwards [(eventually_all_finset S).2 key] with t ht n hn
  exact ht _ hn n rfl

/-- Points slightly to the left of `x` avoid `S + T ℤ`. -/
theorem eventually_nhdsLT_not_mem {T : ℝ} (hT : 0 < T) (S : Finset ℝ) (x : ℝ) :
    ∀ᶠ t in 𝓝[<] x, ∀ n : ℤ, t + n * T ∉ S := by
  have key : ∀ s ∈ S, ∀ᶠ t in 𝓝[<] x, ∀ n : ℤ, t + n * T ≠ s := by
    intro s _
    have hc : toIcoMod hT (x - T) s ∈ Ico (x - T) (x - T + T) := toIcoMod_mem_Ico hT (x - T) s
    have hc2 : toIcoMod hT (x - T) s < x := by linarith [hc.2]
    filter_upwards [Ioo_mem_nhdsLT hc2] with t ht n htn
    have h : toIcoMod hT (x - T) s = t := by
      rw [toIcoMod_eq_iff]
      refine ⟨⟨hc.1.trans ht.1.le, by linarith [ht.2]⟩, n, ?_⟩
      rw [← htn, zsmul_eq_mul]
    exact absurd h (ne_of_lt ht.1)
  filter_upwards [(eventually_all_finset S).2 key] with t ht n hn
  exact ht _ hn n rfl

/-- Mean value inequality up to the right endpoint, where only a one-sided limit exists. -/
theorem norm_sub_lim_le_right {g : ℝ → ℂ} {a u C : ℝ} {r : ℂ}
    (hd : ∀ t ∈ Ioo a u, DifferentiableAt ℝ g t ∧ ‖deriv g t‖ ≤ C)
    (hr : Tendsto g (𝓝[>] a) (𝓝 r)) {b : ℝ} (hb : b ∈ Ioo a u) :
    ‖g b - r‖ ≤ C * (b - a) := by
  have hlip : ∀ c ∈ Ioo a u, ‖g b - g c‖ ≤ C * ‖b - c‖ := fun c hc =>
    (convex_Ioo a u).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hd t ht).1.hasDerivAt.hasDerivWithinAt) (fun t ht => (hd t ht).2) hc hb
  have h1 : Tendsto (fun c => ‖g b - g c‖) (𝓝[>] a) (𝓝 ‖g b - r‖) :=
    (tendsto_const_nhds.sub hr).norm
  have h2 : Tendsto (fun c : ℝ => C * ‖b - c‖) (𝓝[>] a) (𝓝 (C * ‖b - a‖)) := by
    have : Tendsto (fun c : ℝ => c) (𝓝[>] a) (𝓝 a) := nhdsWithin_le_nhds
    exact ((tendsto_const_nhds.sub this).norm).const_mul C
  have h3 := le_of_tendsto_of_tendsto h1 h2 (by
    filter_upwards [Ioo_mem_nhdsGT hb.1] with c hc
    exact hlip c ⟨hc.1, hc.2.trans hb.2⟩)
  rwa [Real.norm_eq_abs, abs_of_pos (sub_pos.2 hb.1)] at h3

/-- Mean value inequality up to the left endpoint, where only a one-sided limit exists. -/
theorem norm_sub_lim_le_left {g : ℝ → ℂ} {a u C : ℝ} {l : ℂ}
    (hd : ∀ t ∈ Ioo u a, DifferentiableAt ℝ g t ∧ ‖deriv g t‖ ≤ C)
    (hl : Tendsto g (𝓝[<] a) (𝓝 l)) {b : ℝ} (hb : b ∈ Ioo u a) :
    ‖g b - l‖ ≤ C * (a - b) := by
  have hlip : ∀ c ∈ Ioo u a, ‖g b - g c‖ ≤ C * ‖b - c‖ := fun c hc =>
    (convex_Ioo u a).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hd t ht).1.hasDerivAt.hasDerivWithinAt) (fun t ht => (hd t ht).2) hc hb
  have h1 : Tendsto (fun c => ‖g b - g c‖) (𝓝[<] a) (𝓝 ‖g b - l‖) :=
    (tendsto_const_nhds.sub hl).norm
  have h2 : Tendsto (fun c : ℝ => C * ‖b - c‖) (𝓝[<] a) (𝓝 (C * ‖b - a‖)) := by
    have : Tendsto (fun c : ℝ => c) (𝓝[<] a) (𝓝 a) := nhdsWithin_le_nhds
    exact ((tendsto_const_nhds.sub this).norm).const_mul C
  have h3 := le_of_tendsto_of_tendsto h1 h2 (by
    filter_upwards [Ioo_mem_nhdsLT hb.2] with c hc
    exact hlip c ⟨hb.1.trans hc.1, hc.2⟩)
  rwa [Real.norm_eq_abs, abs_sub_comm, abs_of_pos (sub_pos.2 hb.2)] at h3

/-- `|e^{2 π i y} - 1| ≥ 4 y` on `(0, 1/2]`. -/
theorem four_mul_le_norm_exp_sub_one {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) (1 / 2)) :
    4 * y ≤ ‖Complex.exp (twoPiI * (y : ℂ)) - 1‖ := by
  have heq : twoPiI * (y : ℂ) = Complex.I * ((2 * Real.pi * y : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    show 2 * Real.pi * y / 2 = Real.pi * y by ring]
  have hpy : Real.pi * y ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, hy.2]
  have hs : 2 / Real.pi * (Real.pi * y) ≤ Real.sin (Real.pi * y) :=
    Real.mul_le_sin (by nlinarith [Real.pi_pos, hy.1]) hpy
  have h2 : 2 / Real.pi * (Real.pi * y) = 2 * y := by
    field_simp
  rw [abs_of_nonneg (by nlinarith [hy.1])]
  linarith

end Sol_FourierSeries_tendsto_symmetric_partial_sums_of_piecewise_C1

open MeasureTheory Set Sol_FourierSeries_tendsto_symmetric_partial_sums_of_piecewise_C1

theorem solution
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℂ) (hper : Function.Periodic f T)
    (S : Finset ℝ)
    (hC1 : ∀ x : ℝ, (∀ n : ℤ, x + n * T ∉ S) →
      DifferentiableAt ℝ f x ∧ ContinuousAt (deriv f) x)
    (hlim : ∀ x : ℝ, ∃ l r : ℂ, Tendsto f (𝓝[<] x) (𝓝 l) ∧ Tendsto f (𝓝[>] x) (𝓝 r))
    (hlim' : ∀ x : ℝ, ∃ l r : ℂ,
      Tendsto (deriv f) (𝓝[<] x) (𝓝 l) ∧ Tendsto (deriv f) (𝓝[>] x) (𝓝 r))
    (x : ℝ) (l r : ℂ) (hl : Tendsto f (𝓝[<] x) (𝓝 l)) (hr : Tendsto f (𝓝[>] x) (𝓝 r)) :
    Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (((1 / T : ℝ) : ℂ) *
            ∫ t in (0 : ℝ)..T, f t * Complex.exp (-(2 * π * Complex.I * n * t / T))) *
          Complex.exp (2 * π * Complex.I * n * x / T))
      atTop (𝓝 ((l + r) / 2)) := by
  -- the exceptional set `S + T ℤ` is countable, and `f` is continuous off it
  set E : Set ℝ := {t | ∃ n : ℤ, t + n * T ∈ S} with hE_def
  have hE : E.Countable := by
    have hEq : E = ⋃ n : ℤ, (fun t : ℝ => t + n * T) ⁻¹' (S : Set ℝ) := by
      ext t
      simp [E]
    rw [hEq]
    exact countable_iUnion fun n => (S.countable_toSet).preimage (add_left_injective _)
  have hfc : ∀ t ∉ E, ContinuousAt f t := fun t ht =>
    (hC1 t (fun n hn => ht ⟨n, hn⟩)).1.continuousAt
  obtain ⟨B, hB⟩ := exists_global_bound hT hper hlim
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hFm : ∀ a c : ℝ, c ≠ 0 → AEStronglyMeasurable (fun y => f (a + c * y)) volume := by
    intro a c hc
    refine aestronglyMeasurable_of_continuousAt_off_countable
      (C := (fun y : ℝ => a + c * y) ⁻¹' E) ?_ ?_
    · refine hE.preimage ?_
      intro y z hyz
      have : c * y = c * z := by simpa using hyz
      exact mul_left_cancel₀ hc this
    · intro y hy
      exact ContinuousAt.comp (g := f) (f := fun y : ℝ => a + c * y) (hfc _ hy)
        ((by fun_prop : Continuous fun y : ℝ => a + c * y).continuousAt)
  -- the function `F y = f (x - T y)`
  set F : ℝ → ℂ := fun y => f (x - T * y) with hF_def
  have hFmeas : AEStronglyMeasurable F volume := by
    have h := hFm x (-T) (neg_ne_zero.2 hT.ne')
    have hfun : (fun y : ℝ => f (x + -T * y)) = F := by
      ext y
      simp only [F]
      congr 1
      ring
    rwa [hfun] at h
  have hFint : IntervalIntegrable F volume (-(1 / 2)) (1 / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hFmeas
      (M := B) (Eventually.of_forall fun y => hB _)
  -- one-sided Lipschitz bounds at `x`
  obtain ⟨u, hu, Cr, hCr0, hCr⟩ : ∃ u > x, ∃ C, 0 ≤ C ∧ ∀ b ∈ Ioo x u, ‖f b - r‖ ≤ C * (b - x) := by
    obtain ⟨l', r', -, hr'⟩ := hlim' x
    have hev : ∀ᶠ t in 𝓝[>] x, DifferentiableAt ℝ f t ∧ ‖deriv f t‖ ≤ ‖r'‖ + 1 := by
      filter_upwards [eventually_nhdsGT_not_mem hT S x,
        hr'.norm.eventually (gt_mem_nhds (lt_add_one _))] with t ht1 ht2
      exact ⟨(hC1 t ht1).1, ht2.le⟩
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    exact ⟨u, hu, _, by positivity, fun b hb => norm_sub_lim_le_right (fun t ht => hsub ht) hr hb⟩
  obtain ⟨v, hv, Cl, hCl0, hCl⟩ : ∃ v < x, ∃ C, 0 ≤ C ∧ ∀ b ∈ Ioo v x, ‖f b - l‖ ≤ C * (x - b) := by
    obtain ⟨l', r', hl', -⟩ := hlim' x
    have hev : ∀ᶠ t in 𝓝[<] x, DifferentiableAt ℝ f t ∧ ‖deriv f t‖ ≤ ‖l'‖ + 1 := by
      filter_upwards [eventually_nhdsLT_not_mem hT S x,
        hl'.norm.eventually (gt_mem_nhds (lt_add_one _))] with t ht1 ht2
      exact ⟨(hC1 t ht1).1, ht2.le⟩
    obtain ⟨v, hv, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hev
    exact ⟨v, hv, _, by positivity, fun b hb => norm_sub_lim_le_left (fun t ht => hsub ht) hl hb⟩
  -- the bound on the symmetric numerator
  set L : ℂ := (l + r) / 2 with hL_def
  set ρ : ℝ := min (u - x) (x - v) with hρ_def
  have hρ : 0 < ρ := lt_min (sub_pos.2 hu) (sub_pos.2 hv)
  set K : ℝ := (Cl + Cr) * T + (2 * B + 2 * ‖L‖) * T / ρ with hK_def
  have hK0 : 0 ≤ K := by positivity
  have hnum : ∀ y ∈ Ioc (0 : ℝ) (1 / 2), ‖F y + F (-y) - 2 * L‖ ≤ K * y := by
    intro y hy
    have hTy : 0 < T * y := mul_pos hT hy.1
    have hFy : F (-y) = f (x + T * y) := by
      simp only [F]
      congr 1
      ring
    by_cases h : T * y < ρ
    · have h1 : ‖F y - l‖ ≤ Cl * (T * y) := by
        have hmem : x - T * y ∈ Ioo v x := by
          constructor
          · have := min_le_right (u - x) (x - v)
            linarith
          · linarith
        have := hCl _ hmem
        simpa [F] using this
      have h2 : ‖F (-y) - r‖ ≤ Cr * (T * y) := by
        have hmem : x + T * y ∈ Ioo x u := by
          constructor
          · linarith
          · have := min_le_left (u - x) (x - v)
            linarith
        have := hCr _ hmem
        rw [hFy]
        simpa using this
      have hsplit : F y + F (-y) - 2 * L = (F y - l) + (F (-y) - r) := by
        simp only [hL_def]
        ring
      rw [hsplit]
      calc ‖(F y - l) + (F (-y) - r)‖ ≤ ‖F y - l‖ + ‖F (-y) - r‖ := norm_add_le _ _
        _ ≤ Cl * (T * y) + Cr * (T * y) := add_le_add h1 h2
        _ = (Cl + Cr) * T * y := by ring
        _ ≤ K * y := by
          apply mul_le_mul_of_nonneg_right _ hy.1.le
          simp only [hK_def]
          have : 0 ≤ (2 * B + 2 * ‖L‖) * T / ρ := by positivity
          linarith
    · push Not at h
      have hbig : ‖F y + F (-y) - 2 * L‖ ≤ 2 * B + 2 * ‖L‖ := by
        calc ‖F y + F (-y) - 2 * L‖ ≤ ‖F y + F (-y)‖ + ‖2 * L‖ := norm_sub_le _ _
          _ ≤ (‖F y‖ + ‖F (-y)‖) + ‖2 * L‖ := add_le_add_left (norm_add_le _ _) _
          _ ≤ (B + B) + 2 * ‖L‖ := by
            gcongr
            · exact hB _
            · exact hB _
            · simp
          _ = 2 * B + 2 * ‖L‖ := by ring
      have hratio : 1 ≤ T * y / ρ := by rw [le_div_iff₀ hρ]; linarith
      calc ‖F y + F (-y) - 2 * L‖ ≤ 2 * B + 2 * ‖L‖ := hbig
        _ ≤ (2 * B + 2 * ‖L‖) * (T * y / ρ) := by
          have : 0 ≤ 2 * B + 2 * ‖L‖ := by positivity
          nlinarith
        _ = (2 * B + 2 * ‖L‖) * T / ρ * y := by ring
        _ ≤ K * y := by
          apply mul_le_mul_of_nonneg_right _ hy.1.le
          simp only [hK_def]
          have : 0 ≤ (Cl + Cr) * T := by positivity
          linarith
  -- integrability of the quotient
  have hquot : IntegrableOn
      (fun y : ℝ => (F y + F (-y) - 2 * L) / (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) - 1))
      (Ioc 0 (1 / 2)) := by
    have hN : AEStronglyMeasurable (fun y => F y + F (-y) - 2 * L) volume := by
      have h2 := hFm x T hT.ne'
      have hfun : (fun y => F y + F (-y) - 2 * L) = fun y => (F y + f (x + T * y)) - 2 * L := by
        ext y
        simp only [F]
        congr 3
        ring
      rw [hfun]
      exact (hFmeas.add h2).sub aestronglyMeasurable_const
    have hD : AEStronglyMeasurable
        (fun y : ℝ => (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) - 1)⁻¹) volume :=
      (Measurable.inv (by fun_prop)).aestronglyMeasurable
    have hQ : AEStronglyMeasurable (fun y : ℝ => (F y + F (-y) - 2 * L) /
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) - 1)) volume := by
      refine (hN.mul hD).congr (Eventually.of_forall fun y => ?_)
      simp only [Pi.mul_apply, div_eq_mul_inv]
    refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hQ (M := K / 4) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun y hy => ?_
    have hden := four_mul_le_norm_exp_sub_one hy
    have hpos : 0 < 4 * y := by linarith [hy.1]
    rw [norm_div, div_le_iff₀ (hpos.trans_le hden)]
    calc ‖F y + F (-y) - 2 * L‖ ≤ K * y := hnum y hy
      _ = K / 4 * (4 * y) := by ring
      _ ≤ K / 4 * ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (y : ℂ)) - 1‖ :=
        mul_le_mul_of_nonneg_left hden (by positivity)
  have hcore := tendsto_symmetric_fourier_integrals_of_integrable_quotient hFint hquot
  -- each Fourier term is an integral against `F`
  have hterm : ∀ n : ℤ,
      (((1 / T : ℝ) : ℂ) *
          ∫ t in (0 : ℝ)..T, f t * Complex.exp (-(2 * π * Complex.I * n * t / T))) *
        Complex.exp (2 * π * Complex.I * n * x / T) =
      ∫ y in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), Complex.exp (2 * π * Complex.I * n * y) * F y := by
    intro n
    have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT.ne'
    set g : ℝ → ℂ := fun t => f t * Complex.exp (-(2 * π * Complex.I * n * t / T)) with hg_def
    have hg : Function.Periodic g T := by
      intro t
      simp only [g]
      rw [hper t]
      congr 1
      have harg : -(2 * π * Complex.I * n * ((t + T : ℝ) : ℂ) / T) =
          -(2 * π * Complex.I * n * t / T) + ((-n : ℤ) : ℂ) * (2 * π * Complex.I) := by
        push_cast
        field_simp
        ring
      rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have h1 : ∫ t in (0 : ℝ)..T, g t = ∫ t in (x - T / 2)..(x + T / 2), g t := by
      have h := hg.intervalIntegral_add_eq 0 (x - T / 2)
      rw [zero_add] at h
      rw [h]
      congr 1
      ring
    have h2 : ∫ y in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), g (-T * y + x) =
        T⁻¹ • ∫ t in (x - T / 2)..(x + T / 2), g t := by
      rw [intervalIntegral.integral_comp_mul_add g (neg_ne_zero.2 hT.ne')]
      have e1 : -T * (-(1 / 2) : ℝ) + x = x + T / 2 := by ring
      have e2 : -T * (1 / 2 : ℝ) + x = x - T / 2 := by ring
      rw [e1, e2, intervalIntegral.integral_symm, smul_neg, inv_neg, neg_smul, neg_neg]
    calc (((1 / T : ℝ) : ℂ) * ∫ t in (0 : ℝ)..T, g t) * Complex.exp (2 * π * Complex.I * n * x / T)
        = (∫ y in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), g (-T * y + x)) *
            Complex.exp (2 * π * Complex.I * n * x / T) := by
          rw [h2, h1, Complex.real_smul, one_div]
      _ = ∫ y in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), g (-T * y + x) *
            Complex.exp (2 * π * Complex.I * n * x / T) :=
          (intervalIntegral.integral_mul_const _ _).symm
      _ = ∫ y in (-(1 / 2) : ℝ)..(1 / 2 : ℝ), Complex.exp (2 * π * Complex.I * n * y) * F y := by
          apply intervalIntegral.integral_congr
          intro y _
          simp only [g, F]
          rw [show -T * y + x = x - T * y by ring, mul_comm (Complex.exp _) (f _), mul_assoc,
            ← Complex.exp_add]
          congr 2
          push_cast
          field_simp
          ring
  refine hcore.congr fun N => ?_
  exact Finset.sum_congr rfl fun n _ => (hterm n).symm
