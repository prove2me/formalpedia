-- Prove2me | solution 1 for ExplicitFormula.poisson_summation_mellin_of_piecewise_smooth
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:38:55.219618+00:00
-- url     : https://prove2.me/submissions/79b12c22-612e-4a07-a5f8-a2086b8a9fbc

import Mathlib

open Filter Topology
open scoped Real ContDiff

set_option autoImplicit false

namespace Sol_ExplicitFormula_poisson_summation_mellin_of_piecewise_smooth

open Set MeasureTheory
open scoped FourierTransform

local notation "logMellin" =>
  (fun (f : ℝ → ℂ) ↦ mellin (fun t ↦ f (Real.log t)))
local notation "twoPiI" => (2 * (Real.pi : ℂ) * Complex.I)

theorem integral_comp_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    ∫ x, Real.exp x • g (Real.exp x) = ∫ y in Ioi 0, g y := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp] at h
  simpa [abs_of_pos (Real.exp_pos _)] using h.symm

theorem integrable_comp_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E) :
    Integrable (fun x ↦ Real.exp x • g (Real.exp x)) ↔ IntegrableOn g (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp] at h
  simpa [abs_of_pos (Real.exp_pos _)] using h.symm

theorem integrableOn_comp_log_Ioi_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) :
    IntegrableOn (fun x ↦ x⁻¹ • g (Real.log x)) (Ioi 0) ↔ Integrable g := by
  rw [← integrable_comp_exp]
  refine integrable_congr (Eventually.of_forall fun x ↦ ?_)
  simp [smul_smul, (Real.exp_pos x).ne']

/-- A logarithmic profile has an absolutely convergent Mellin integral at `s` if its
exponential weight at the real part of `s` is integrable on the real line. -/
theorem mellinConvergent_of_integrable_logWeight (f : ℝ → ℂ) (s : ℂ)
    (h : Integrable (fun x : ℝ ↦ (Real.exp (s.re * x) : ℂ) * f x)) :
    MellinConvergent (fun t ↦ f (Real.log t)) s := by
  let phase (x : ℝ) := Complex.exp ((x : ℂ) * (s - s.re))
  have hc : Continuous phase := by
    dsimp [phase]
    fun_prop
  have hunit (x : ℝ) : ‖phase x‖ ≤ 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re]
  apply (integrable_comp_exp _).mp
  apply (h.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall hunit)).congr
  filter_upwards with x
  simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  simp only [phase, Complex.ofReal_exp, Complex.ofReal_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring



/-- Integration over a fundamental interval unfolds the integer periodization of an integrable
function against any integer frequency. -/
theorem integral_periodization_mul_exp_int {g : ℝ → ℂ} (hg : Integrable g) (k : ℤ) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2 : ℝ),
        Complex.exp (twoPiI * (k : ℂ) * (x : ℂ)) * (∑' n : ℤ, g (x + n))) =
      ∫ x : ℝ, Complex.exp (twoPiI * (k : ℂ) * (x : ℂ)) * g x := by
  let e (x : ℝ) := Complex.exp (twoPiI * (k : ℂ) * (x : ℂ))
  have he : Continuous e := by dsimp [e]; fun_prop
  have hen (x : ℝ) : ‖e x‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have headd (x : ℝ) (n : ℤ) : e (x + n) = e x := by
    have heint : Complex.exp (twoPiI * (k : ℂ) * (n : ℂ)) = 1 := by
      simpa [Int.cast_mul, mul_assoc, mul_left_comm, mul_comm] using
        Complex.exp_int_mul_two_pi_mul_I (k * n)
    simp [e, Complex.ofReal_add, mul_add, Complex.exp_add, heint]
  let G (x : ℝ) := e x * g x
  have hG : Integrable G := hg.bdd_mul he.aestronglyMeasurable (Eventually.of_forall (fun x ↦ (hen x).le))
  let a : ℝ := -(1 / 2)
  let b : ℝ := 1 / 2
  have hab : a ≤ b := by norm_num [a, b]
  have hshift {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {F : ℝ → E} (hF : Integrable F) :
      HasSum (fun n : ℤ ↦ ∫ x in a..b, F (x + n)) (∫ x, F x) := by
    convert hF.hasSum_intervalIntegral a using 1
    ext n
    rw [intervalIntegral.integral_comp_add_right]
    congr 1
    dsimp [a, b]
    ring
  have hGi (n : ℤ) : IntegrableOn (fun x : ℝ ↦ G (x + n)) (Ioc a b) :=
    (hG.comp_add_right (n : ℝ)).integrableOn
  have hnorm : Summable (fun n : ℤ ↦ ∫ x in Ioc a b, ‖G (x + n)‖) := by
    simpa only [intervalIntegral.integral_of_le hab] using (hshift hG.norm).summable
  change (∫ x in a..b, e x * (∑' n : ℤ, g (x + n))) = ∫ x, G x
  have hterm (x : ℝ) (n : ℤ) : e x * g (x + n) = G (x + n) := by
    change e x * g (x + n) = e (x + n) * g (x + n)
    rw [headd]
  simp_rw [intervalIntegral.integral_of_le hab, ← tsum_mul_left, hterm]
  rw [← integral_tsum_of_summable_integral_norm hGi hnorm]
  simpa only [intervalIntegral.integral_of_le hab] using (hshift hG).tsum_eq

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


/-- A small punctured neighborhood of every integer avoids a fixed finite set. -/
private theorem exists_radius_avoiding_shifted_finite {S : Set ℝ} (hS : S.Finite) :
    ∃ δ ∈ Ioc (0 : ℝ) 1, ∀ (n : ℤ) (x : ℝ), x ≠ 0 → |x| < δ → x + n ∉ S := by
  obtain ⟨M, hM⟩ := hS.isCompact.isBounded.exists_norm_le
  let B := {n : ℤ | (n : ℝ) ∈ Icc (-(M + 1)) (M + 1)}
  have hB : B.Finite := by
    have he := Int.tendsto_coe_cofinite.eventually
      (isCompact_Icc (a := -(M + 1)) (b := M + 1)).compl_mem_cocompact
    simpa only [eventually_cofinite, mem_compl_iff, not_not, B, mem_ofPred_eq] using he
  have hne (n : ℤ) : ∀ᶠ x in 𝓝 (0 : ℝ), x ≠ 0 → x + (n : ℝ) ∉ S := by
    let T := ((fun x : ℝ ↦ x + (n : ℝ)) ⁻¹' S) \ {(0 : ℝ)}
    have hT : T.Finite :=
      (hS.preimage (add_left_injective (n : ℝ)).injOn).subset sdiff_subset
    have hT₀ : 0 ∈ Tᶜ := fun hx ↦ hx.2 (mem_singleton _)
    filter_upwards [hT.isClosed.isOpen_compl.mem_nhds hT₀] with x hx hx₀ hxS
    exact hx ⟨hxS, hx₀⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hB.eventually_all.mpr (fun n _ ↦ hne n))
  refine ⟨min r 1, ⟨lt_min hr zero_lt_one, min_le_right _ _⟩, ?_⟩
  intro n x hx hxr hxS
  have hx1 : |x| ≤ 1 := (hxr.trans_le (min_le_right _ _)).le
  have hn : n ∈ B := by
    change (n : ℝ) ∈ Icc (-(M + 1)) (M + 1)
    apply abs_le.mp
    calc
      |(n : ℝ)| = |x + (n : ℝ) - x| := by ring_nf
      _ ≤ |x + (n : ℝ)| + |x| := abs_sub _ _
      _ ≤ M + 1 := add_le_add (by simpa only [Real.norm_eq_abs] using hM _ hxS) hx1
  exact hball (by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using
      hxr.trans_le (min_le_left _ _)) n hn hx hxS

/-- Uniform exponential bounds for a profile and its derivative give a Lipschitz
estimate for the symmetric part of its periodization at a lattice point. -/
theorem periodization_bounds_of_exp_decay
    {g : ℝ → ℂ} {S : Set ℝ} (hS : S.Finite) {A b : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hg : ∀ x, ‖g x‖ ≤ A * Real.exp (-b * |x|))
    (hderiv : ∀ x ∉ S, DifferentiableAt ℝ g x ∧ ‖deriv g x‖ ≤ A * Real.exp (-b * |x|))
    {u v : ℤ → ℂ}
    (hu : ∀ n : ℤ, Tendsto (fun x : ℝ ↦ g (x + n)) (𝓝[>] 0) (𝓝 (u n)))
    (hv : ∀ n : ℤ, Tendsto (fun x : ℝ ↦ g (-x + n)) (𝓝[>] 0) (𝓝 (v n))) :
    let F (x : ℝ) := ∑' n : ℤ, g (x + n)
    let L := ∑' n : ℤ, (u n + v n) / 2
    ∃ C ≥ (0 : ℝ),
      (∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ‖F x‖ ≤ C) ∧
      ∀ x ∈ Ioc (0 : ℝ) (1 / 2), ‖F x + F (-x) - 2 * L‖ ≤ C * x := by
  dsimp only
  let F (x : ℝ) := ∑' n : ℤ, g (x + n)
  let B (n : ℤ) := (A * Real.exp b) * Real.exp (|(n : ℝ)| * -b)
  have hB₀ (n : ℤ) : 0 ≤ B n := by dsimp [B]; positivity
  have hBs : Summable B := by
    have hgeom := Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hb)
    apply Summable.mul_left
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor <;> simpa [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hgeom
  let M := ∑' n : ℤ, B n
  have hM : 0 ≤ M := tsum_nonneg hB₀
  have hmaj (n : ℤ) {x : ℝ} (hx : |x| ≤ 1) : A * Real.exp (-b * |x + n|) ≤ B n := by
    have htri : |(n : ℝ)| ≤ |x + n| + |x| := by
      simpa only [add_sub_cancel_left] using (abs_sub (x + (n : ℝ)) x)
    dsimp [B]
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hA.le
    nlinarith only [mul_le_mul_of_nonneg_left htri hb.le, mul_le_mul_of_nonneg_left hx hb.le]
  have hnorm {x : ℝ} (hx : |x| ≤ 1) :
      Summable (fun n : ℤ ↦ ‖g (x + n)‖) :=
    .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ (hg _).trans (hmaj n hx)) hBs
  have hF (x : ℝ) (hx : |x| ≤ 1) : ‖F x‖ ≤ M := by
    exact (norm_tsum_le_tsum_norm (hnorm hx)).trans
      ((hnorm hx).tsum_le_tsum (fun n ↦ (hg _).trans (hmaj n hx)) hBs)
  have hside {w : ℤ → ℂ} {e : ℝ} (he : |e| = 1)
      (hw : ∀ n : ℤ, Tendsto (fun x : ℝ ↦ g (e * x + n)) (𝓝[>] 0) (𝓝 (w n))) :
      ∀ n : ℤ, ‖w n‖ ≤ B n := by
    intro n
    apply le_of_tendsto (hw n).norm
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with x hx
    exact (hg _).trans (hmaj n (by simpa [abs_mul, he, abs_of_pos hx.1] using hx.2.le))
  have hule := hside (e := 1) (by norm_num) (by simpa using hu)
  have hvle := hside (e := -1) (by norm_num) (by simpa using hv)
  have hus : Summable (fun n ↦ ‖u n‖) := .of_nonneg_of_le (fun _ ↦ norm_nonneg _) hule hBs
  have hvs : Summable (fun n ↦ ‖v n‖) := .of_nonneg_of_le (fun _ ↦ norm_nonneg _) hvle hBs
  have huSum : ‖∑' n, u n‖ ≤ M :=
    (norm_tsum_le_tsum_norm hus).trans (hus.tsum_le_tsum hule hBs)
  have hvSum : ‖∑' n, v n‖ ≤ M :=
    (norm_tsum_le_tsum_norm hvs).trans (hvs.tsum_le_tsum hvle hBs)
  obtain ⟨δ, hδ, hnoCut⟩ := exists_radius_avoiding_shifted_finite hS
  have hδpos : 0 < δ := hδ.1
  have hlarge : 0 ≤ 4 * M / δ := div_nonneg (mul_nonneg (by norm_num) hM) hδpos.le
  have hslope {w : ℤ → ℂ} {e : ℝ} (he : |e| = 1)
      (hw : ∀ n : ℤ, Tendsto (fun x : ℝ ↦ g (e * x + n)) (𝓝[>] 0) (𝓝 (w n)))
      (n : ℤ) {x : ℝ} (hx : x ∈ Ioo 0 δ) :
      ‖g (e * x + n) - w n‖ ≤ B n * x := by
    let p (y : ℝ) := g (e * y + n)
    have hdiff (y : ℝ) (hy : y ∈ Ioo 0 δ) :
        HasDerivAt p (e • deriv g (e * y + n)) y := by
      have hnormE : |e * y| = y := by rw [abs_mul, he, one_mul, abs_of_pos hy.1]
      have hcut := hnoCut n (e * y) (abs_pos.mp (hnormE.symm ▸ hy.1)) (hnormE.symm ▸ hy.2)
      simpa [p, Function.comp_def] using
        ((hderiv _ hcut).1.hasDerivAt.scomp y (((hasDerivAt_id y).const_mul e).add_const (n : ℝ)))
    have hbound (y : ℝ) (hy : y ∈ Ioo 0 δ) : ‖e • deriv g (e * y + n)‖ ≤ B n := by
      have hnormE : |e * y| = y := by rw [abs_mul, he, one_mul, abs_of_pos hy.1]
      have hcut := hnoCut n (e * y) (abs_pos.mp (hnormE.symm ▸ hy.1)) (hnormE.symm ▸ hy.2)
      simpa only [norm_smul, Real.norm_eq_abs, he, one_mul] using
        ((hderiv _ hcut).2.trans (hmaj n (hnormE.symm ▸ hy.2.le.trans hδ.2)))
    have hxlim : Tendsto (fun y : ℝ ↦ B n * ‖x - y‖) (𝓝[>] 0) (𝓝 (B n * x)) := by
      have h₀ : Tendsto (fun y : ℝ ↦ y) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
      simpa [Real.norm_eq_abs, abs_of_pos hx.1] using (h₀.const_sub x).norm.const_mul (B n)
    apply le_of_tendsto_of_tendsto ((hw n).const_sub (p x)).norm hxlim
    filter_upwards [Ioo_mem_nhdsGT hδ.1] with y hy
    exact (convex_Ioo (0 : ℝ) δ).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz ↦ (hdiff z hz).hasDerivWithinAt) hbound hy hx
  have hlimit (x : ℝ) (hx : x ∈ Ioo 0 δ) :
      ‖F x - ∑' n, u n‖ ≤ M * x ∧ ‖F (-x) - ∑' n, v n‖ ≤ M * x := by
    have hx₁ : |x| ≤ 1 := by rw [abs_of_pos hx.1]; exact hx.2.le.trans hδ.2
    have ht (e : ℝ) (he : |e| = 1) (w : ℤ → ℂ) (hs : Summable fun n ↦ ‖w n‖)
        (hw : ∀ n : ℤ, Tendsto (fun y : ℝ ↦ g (e * y + n)) (𝓝[>] 0) (𝓝 (w n))) :
        ‖F (e * x) - ∑' n, w n‖ ≤ M * x := by
      have hBxs := hBs.mul_right x
      have h := hslope he hw (x := x)
      have hr : Summable (fun n : ℤ ↦ ‖g (e * x + n) - w n‖) :=
        .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ h n hx) hBxs
      have hgs := hnorm (x := e * x) (by simpa [abs_mul, he] using hx₁)
      rw [show F (e * x) - ∑' n, w n = ∑' n : ℤ, (g (e * x + n) - w n) from
        (hgs.of_norm.tsum_sub hs.of_norm).symm, ← hBs.tsum_mul_right x]
      exact (norm_tsum_le_tsum_norm hr).trans (hr.tsum_le_tsum (fun n ↦ h n hx) hBxs)
    exact ⟨by simpa using ht 1 (by norm_num) u hus (by simpa using hu),
      by simpa using ht (-1) (by norm_num) v hvs (by simpa using hv)⟩
  let C := M + 2 * M + 4 * M / δ
  have hCM : M ≤ C := by
    dsimp [C]
    linarith only [hM, hlarge]
  refine ⟨C, hM.trans hCM, ?_, ?_⟩
  · intro x hx
    have hx₁ : |x| ≤ 1 := (abs_le.mpr hx).trans (by norm_num)
    exact (hF x hx₁).trans hCM
  · intro x hx
    have hx₁ : |x| ≤ 1 := by rw [abs_of_pos hx.1]; exact hx.2.trans (by norm_num)
    have hrewrite :
        2 * (∑' n, (u n + v n) / 2) = (∑' n, u n) + (∑' n, v n) := by
      rw [← tsum_mul_left]
      have htwo (n : ℤ) : (2 : ℂ) * ((u n + v n) / 2) = u n + v n := by ring
      simp_rw [htwo]
      exact hus.of_norm.tsum_add hvs.of_norm
    simp only [hrewrite]
    rw [show F x + F (-x) - ((∑' n, u n) + ∑' n, v n) =
      (F x - ∑' n, u n) + (F (-x) - ∑' n, v n) by ring]
    apply (norm_add_le _ _).trans
    by_cases h : x < δ
    · obtain ⟨h₁, h₂⟩ := hlimit x ⟨hx.1, h⟩
      exact (add_le_add h₁ h₂).trans (by
        dsimp [C]
        nlinarith [mul_nonneg hM hx.1.le, mul_nonneg hlarge hx.1.le])
    · have h₁ := (norm_sub_le _ _).trans (add_le_add (hF x hx₁) huSum)
      have h₂ := (norm_sub_le _ _).trans (add_le_add (hF (-x) (by rwa [abs_neg])) hvSum)
      have hbig : 4 * M ≤ (4 * M / δ) * x := by
        calc
          4 * M = (4 * M / δ) * δ := by field_simp [hδ.1.ne']
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_of_not_gt h) hlarge
      exact (add_le_add h₁ h₂).trans (by
        dsimp [C]
        nlinarith [mul_nonneg hM hx.1.le])


/-- Paper: Lemma B.4.1.1(1)–(2), p. 607. The logarithmic profile is smooth
off a finite set and all its derivatives have finite one-sided limits there.
The profile and its first derivative decay faster than every exponential on
both tails, as in (B.4.1.1). -/
def IsPiecewiseSmoothMellinTest (f : ℝ → ℂ) : Prop :=
  (∃ S : Finset ℝ, ContDiffOn ℝ ∞ f (S : Set ℝ)ᶜ ∧
    ∀ (j : ℕ) (x : ℝ), x ∈ S →
      (∃ l : ℂ, Tendsto (iteratedDeriv j f) (𝓝[<] x) (𝓝 l)) ∧
      (∃ r : ℂ, Tendsto (iteratedDeriv j f) (𝓝[>] x) (𝓝 r))) ∧
  ∀ N : ℕ, ∃ C > (0 : ℝ), ∃ T > (0 : ℝ), ∀ x : ℝ, T < |x| →
    ‖f x‖ < C * Real.exp (-(N : ℝ) * |x|) ∧
    ‖deriv f x‖ < C * Real.exp (-(N : ℝ) * |x|)

/-- Paper: Lemma B.4.1.1, p. 607. The Mellin integral (B.4.1.2) of a test
function with finitely many jumps converges absolutely for every exponent. -/
theorem mellinConvergent_of_piecewiseSmoothMellinTest
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) (s : ℂ) :
    MellinConvergent (fun t ↦ f (Real.log t)) s := by
  obtain ⟨⟨S, hsmooth, hlimits⟩, hdecay⟩ := hf
  apply mellinConvergent_of_integrable_logWeight
  let w (x : ℝ) : ℂ := Real.exp (s.re * x)
  let g (x : ℝ) := w x * f x
  change Integrable g
  have hw : Continuous w := by
    dsimp [w]
    fun_prop
  have hcont : ContinuousOn g (S : Set ℝ)ᶜ :=
    hw.continuousOn.mul hsmooth.continuousOn
  have hmeas : Measurable g :=
    measurable_of_measurable_on_compl_finite _ S.finite_toSet
      (continuousOn_iff_continuous_domRestrict.mp hcont).measurable
  -- The weighted profile is locally integrable even at the jumps.
  have hloc : LocallyIntegrable g := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨⟨l, hl⟩, ⟨r, hr⟩⟩ := hlimits 0 x hx
      simp only [iteratedDeriv_zero] at hl hr
      rw [← nhdsNE_sup_pure x, ← nhdsLT_sup_nhdsGT x, IntegrableAtFilter.sup_iff,
        IntegrableAtFilter.sup_iff]
      have hside {u : Set ℝ} {a : ℂ} (hu : MeasurableSet u)
          (ha : Tendsto f (𝓝[u] x) (𝓝 a)) : IntegrableAtFilter g (𝓝[u] x) volume := by
        have := hu.nhdsWithin_isMeasurablyGenerated x
        exact ((hw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul ha).integrableAtFilter
          hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter (volume.finiteAt_nhdsWithin x u)
      exact ⟨⟨hside measurableSet_Iio hl, hside measurableSet_Ioi hr⟩,
        ⟨{x}, by simp, integrableOn_singleton (hx := measure_singleton_lt_top)⟩⟩
    · have hx' : (S : Set ℝ)ᶜ ∈ 𝓝 x :=
        S.finite_toSet.isClosed.isOpen_compl.mem_nhds hx
      exact ((hcont x hx).continuousAt hx').integrableAtFilter
        hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter (volume.finiteAt_nhds x)
  -- Dominate both tails by a constant times exp (-|x|).
  obtain ⟨N, hN⟩ := exists_nat_gt (|s.re| + 1)
  obtain ⟨C, hC, T, hT, htail⟩ := hdecay N
  have hbound (x : ℝ) (hx : T < |x|) : ‖g x‖ ≤ C * Real.exp (-|x|) := by
    have hprod : s.re * x ≤ |s.re| * |x| := by
      rw [← abs_mul]
      exact le_abs_self _
    have hrate : (|s.re| + 1) * |x| ≤ (N : ℝ) * |x| :=
      mul_le_mul_of_nonneg_right hN.le (abs_nonneg x)
    rw [show ‖g x‖ = Real.exp (s.re * x) * ‖f x‖ by
      simp only [g, w, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]]
    calc
      _ ≤ Real.exp (s.re * x) * (C * Real.exp (-(N : ℝ) * |x|)) :=
        mul_le_mul_of_nonneg_left (htail x hx).1.le (Real.exp_pos _).le
      _ = C * Real.exp (s.re * x + -(N : ℝ) * |x|) := by rw [Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hprod, hrate])) hC.le
  refine integrable_iff_integrableAtFilter_atBot_atTop.mpr ⟨⟨?_, ?_⟩, hloc⟩
  · refine ⟨Iio (-T), Iio_mem_atBot _, ?_⟩
    refine (((integrableOn_exp_Iic (-T)).mono_set Iio_subset_Iic_self).const_mul C).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    have hx' : x < -T := hx
    have hneg : x < 0 := hx'.trans (neg_neg_of_pos hT)
    have hTx : T < -x := by linarith only [hx']
    simpa only [abs_of_neg hneg, neg_neg] using
      hbound x (by rwa [abs_of_neg hneg])
  · refine ⟨Ioi T, Ioi_mem_atTop _, ?_⟩
    refine ((integrableOn_exp_neg_Ioi T).const_mul C).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hpos : 0 < x := hT.trans hx
    simpa [abs_of_pos hpos] using hbound x (by simpa [abs_of_pos hpos] using hx)

/-- Paper: Proposition B.4.1.2, p. 608. At a point with both one-sided limits,
the sample used for Poisson summation is their arithmetic mean. -/
noncomputable def mellinJumpMidpoint (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (limUnder (𝓝[<] x) f + limUnder (𝓝[>] x) f) / 2

/-- Paper: Proposition B.4.1.2, p. 608. When the two one-sided limits are
given, the midpoint sample is their average.
Deviation: Sanity check for the normalization of the midpoint. -/
theorem mellinJumpMidpoint_eq_average {f : ℝ → ℂ} {x : ℝ} {l r : ℂ}
    (hl : Tendsto f (𝓝[<] x) (𝓝 l)) (hr : Tendsto f (𝓝[>] x) (𝓝 r)) :
    mellinJumpMidpoint f x = (l + r) / 2 := by
  rw [mellinJumpMidpoint, hl.limUnder_eq, hr.limUnder_eq]

/-- Paper: Proposition B.4.1.2, p. 608. The unitary character's weighted
midpoint samples on the multiplicative lattice are absolutely summable.
The value `c` on the generator determines the character. -/
theorem summable_mellinJumpMidpoint_lattice
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ ≠ 1) (c : Circle) :
    Summable (fun m : ℤ ↦ (c : ℂ) ^ m * mellinJumpMidpoint f ((m : ℝ) * Real.log θ)) := by
  obtain ⟨⟨S, hsmooth, _⟩, hdecay⟩ := hf
  obtain ⟨C, _, T, _, htail⟩ := hdecay 1
  have hlog := Real.log_ne_zero_of_pos_of_ne_one hθ hθ₁
  have hgeom : Summable (fun n : ℕ ↦ Real.exp ((n : ℝ) * -|Real.log θ|)) :=
    Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr (abs_pos.mpr hlog))
  have hsum : Summable (fun m : ℤ ↦ Real.exp (|(m : ℝ)| * -|Real.log θ|)) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor <;> simpa [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using hgeom
  apply (hsum.mul_left C).of_norm_bounded_eventually
  have hlattice : Tendsto (fun m : ℤ ↦ (m : ℝ) * Real.log θ) cofinite (cocompact ℝ) := by
    have h : Tendsto (fun m : ℤ ↦ zmultiplesHom ℝ (Real.log θ) m) cofinite (cocompact ℝ) :=
      Int.tendsto_zmultiplesHom_cofinite hlog
    simpa only [zmultiplesHom_apply, zsmul_eq_mul] using h
  have habs : Tendsto (fun m : ℤ ↦ |(m : ℝ) * Real.log θ|) cofinite atTop := by
    simpa only [Function.comp_def, Real.norm_eq_abs] using
      tendsto_norm_cocompact_atTop.comp hlattice
  filter_upwards [hlattice.eventually S.finite_toSet.isCompact.compl_mem_cocompact,
    habs.eventually_gt_atTop T] with m hmS hmT
  have hcont := hsmooth.continuousOn.continuousAt
    (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hmS)
  rw [mellinJumpMidpoint_eq_average (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (hcont.tendsto.mono_left nhdsWithin_le_nhds), add_self_div_two,
    Complex.norm_mul, Complex.norm_zpow, Circle.norm_coe, one_zpow, one_mul]
  simpa only [Nat.cast_one, neg_one_mul, abs_mul, mul_neg] using
    (htail ((m : ℝ) * Real.log θ) hmT).1.le

-- TODO(paper-gap): (B.4.1.7) has the wrong sign for 0 < θ < 1.
-- With θ = 1/2, the trivial character and the indicator of [1, 2],
-- its two sides are -log 2 and log 2.
-- TODO(paper-gap): The exponent ix called log χ(θ) on p. 607 must be
-- multiplied by log θ to give the complex logarithm in (B.4.1.7).
-- TODO(paper-gap): (B.4.1.15) drops the character twist at the translated point,
-- and (B.4.1.17) omits the midpoint contributions from |m| ≤ N₀.

open MeasureTheory in
/-- The Mellin samples in the logarithmic coordinate are the Fourier integrals of the
rescaled, twisted profile, with the absolute Jacobian of the rescaling. -/
private theorem logMellin_eq_mul_integral_twist (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0)
    (ℓ : ℂ) (m : ℤ) :
    mellin (fun t ↦ f (Real.log t)) ((ℓ + twoPiI * (m : ℂ)) / (a : ℂ)) =
      ((|a| : ℝ) : ℂ) *
        ∫ x : ℝ, Complex.exp (twoPiI * (m : ℂ) * (x : ℂ)) *
          (Complex.exp (ℓ * (x : ℂ)) * f (a * x)) := by
  let s := (ℓ + twoPiI * (m : ℂ)) / (a : ℂ)
  let F (y : ℝ) := Complex.exp (s * y) * f y
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hmellin : mellin (fun t ↦ f (Real.log t)) s = ∫ y, F y := by
    rw [mellin, ← integral_comp_exp]
    apply integral_congr_ae
    filter_upwards with y
    simp only [Real.log_exp, Complex.real_smul, smul_eq_mul]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos y).ne'),
      ← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp]
    simp only [F, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have heq (x : ℝ) :
      Complex.exp (twoPiI * (m : ℂ) * (x : ℂ)) *
        (Complex.exp (ℓ * (x : ℂ)) * f (a * x)) = F (a * x) := by
    simp only [F, Complex.ofReal_mul, ← mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp [s]
    field_simp
    ring
  simp_rw [heq, Measure.integral_comp_mul_left, abs_inv, Complex.real_smul, Complex.ofReal_inv,
    ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr ha)), one_mul]
  exact hmellin

/-- The finite one-sided limits extend the tail estimate to a global bound. -/
private theorem mellinTest_global_exp_bound {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) :
    ∃ A > (0 : ℝ), ∀ x, ‖f x‖ ≤ A * Real.exp (-|x|) ∧
      ‖deriv f x‖ ≤ A * Real.exp (-|x|) := by
  obtain ⟨⟨S, hs, hlimits⟩, hdecay⟩ := hf
  obtain ⟨C, hC, T, _, htail⟩ := hdecay 1
  have hopen : IsOpen (S : Set ℝ)ᶜ := S.finite_toSet.isClosed.isOpen_compl
  have hcompact {g : ℝ → ℂ} (hg : ContinuousOn g (S : Set ℝ)ᶜ)
      (hlim : ∀ x ∈ S, (∃ l, Tendsto g (𝓝[<] x) (𝓝 l)) ∧
        (∃ r, Tendsto g (𝓝[>] x) (𝓝 r))) :
      ∃ B : ℝ, ∀ x ∈ Icc (-T) T, ‖g x‖ ≤ B := by
    have hloc (x : ℝ) : (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ ‖g y‖) := by
      by_cases hx : x ∈ S
      · obtain ⟨⟨l, hl⟩, ⟨r, hr⟩⟩ := hlim x hx
        rw [← nhdsNE_sup_pure x, ← nhdsLT_sup_nhdsGT x, IsBoundedUnder, map_sup, map_sup]
        exact isBounded_sup (isBounded_sup hl.norm.isBoundedUnder_le hr.norm.isBoundedUnder_le)
          ⟨‖g x‖, by simp⟩
      · exact ((hg x hx).continuousAt (hopen.mem_nhds hx)).tendsto.norm.isBoundedUnder_le
    have hbounded : Bornology.IsBounded (g '' Icc (-T) T) := by
      apply Bornology.isBounded_image_of_isLocallyBounded_of_isCompact isCompact_Icc
      intro x
      obtain ⟨B, hB⟩ := hloc x
      exact ⟨{y | ‖g y‖ ≤ B}, eventually_map.mp hB,
        isBounded_iff_forall_norm_le.mpr ⟨B, forall_mem_image.mpr fun _ hy ↦ hy⟩⟩
    obtain ⟨B, hB⟩ := hbounded.exists_norm_le
    exact ⟨B, fun x hx ↦ hB _ (mem_image_of_mem g hx)⟩
  obtain ⟨U, hU⟩ := hcompact hs.continuousOn (by simpa only [iteratedDeriv_zero] using hlimits 0)
  obtain ⟨V, hV⟩ := hcompact (hs.continuousOn_deriv_of_isOpen hopen (by simp))
    (by simpa only [iteratedDeriv_one] using hlimits 1)
  let A := C + (|U| + |V|) * Real.exp T
  have hCA : C ≤ A := le_add_of_nonneg_right (by positivity)
  refine ⟨A, hC.trans_le hCA, fun x ↦ ?_⟩
  by_cases hx : T < |x|
  · obtain ⟨h₀, h₁⟩ := htail x hx
    simp only [Nat.cast_one, neg_one_mul] at h₀ h₁
    exact ⟨h₀.le.trans (mul_le_mul_of_nonneg_right hCA (Real.exp_pos _).le),
      h₁.le.trans (mul_le_mul_of_nonneg_right hCA (Real.exp_pos _).le)⟩
  · have hTx : |x| ≤ T := le_of_not_gt hx
    have hx' := abs_le.mp hTx
    have hcalc (y : ℝ) (hy : y ≤ |U| + |V|) : y ≤ A * Real.exp (-|x|) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
      exact (mul_le_mul hy (Real.exp_le_exp.mpr hTx) (Real.exp_pos _).le (by positivity)).trans
        (le_add_of_nonneg_left hC.le)
    exact ⟨hcalc _ ((hU x hx').trans ((le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _)))),
      hcalc _ ((hV x hx').trans ((le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))))⟩

/-- A unitary twist and a nonzero rescaling preserve exponential bounds off the jumps. -/
private theorem mellinTest_twisted_deriv_bound {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f)
    {a : ℝ} (ha : a ≠ 0) {ℓ : ℂ} (hunit : ℓ.re = 0) :
    let w (x : ℝ) := Complex.exp (ℓ * (x : ℂ))
    let g (x : ℝ) := w x * f (a * x)
    ∃ S : Set ℝ, S.Finite ∧ ∃ A > (0 : ℝ),
      (∀ x, ‖g x‖ ≤ A * Real.exp (-|a| * |x|)) ∧
      ∀ x ∉ S, DifferentiableAt ℝ g x ∧ ‖deriv g x‖ ≤ A * Real.exp (-|a| * |x|) := by
  dsimp only
  obtain ⟨A, hA, hbound⟩ := mellinTest_global_exp_bound hf
  obtain ⟨S, hs, _⟩ := hf.1
  let w (x : ℝ) := Complex.exp (ℓ * (x : ℂ))
  let g (x : ℝ) := w x * f (a * x)
  have hwnorm (x : ℝ) : ‖w x‖ = 1 := by simp [w, Complex.norm_exp, Complex.mul_re, hunit]
  let M := (1 + ‖ℓ‖ + |a|) * A
  have hM : A ≤ M := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 1 + ‖ℓ‖ + |a| by
        linarith [norm_nonneg ℓ, abs_nonneg a]) hA.le
  refine ⟨(fun x : ℝ ↦ a * x) ⁻¹' (S : Set ℝ), ?_, M, hA.trans_le hM, ?_, ?_⟩
  · exact S.finite_toSet.preimage (mul_right_injective₀ ha).injOn
  · intro x
    change ‖w x * f (a * x)‖ ≤ _
    rw [norm_mul, hwnorm, one_mul, neg_mul, ← abs_mul]
    exact (hbound _).1.trans (mul_le_mul_of_nonneg_right hM (Real.exp_pos _).le)
  · intro x hx
    have hf' := ((hs (a * x) hx).contDiffAt
      (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hx)).differentiableAt (by simp)
    have hw' := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul ℓ).cexp
    have hcom := hf'.hasDerivAt.scomp x ((hasDerivAt_id x).const_mul a)
    have hderiv : HasDerivAt g (w x * (ℓ * f (a * x) + (a : ℂ) * deriv f (a * x))) x := by
      refine (hw'.mul hcom).congr_deriv ?_
      simp [w, Complex.real_smul]
      ring
    refine ⟨hderiv.differentiableAt, ?_⟩
    rw [hderiv.deriv, norm_mul, hwnorm, one_mul, neg_mul, ← abs_mul]
    calc
      _ ≤ ‖ℓ‖ * ‖f (a * x)‖ + |a| * ‖deriv f (a * x)‖ := by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
          norm_add_le (ℓ * f (a * x)) ((a : ℂ) * deriv f (a * x))
      _ ≤ ‖ℓ‖ * (A * Real.exp (-|a * x|)) + |a| * (A * Real.exp (-|a * x|)) :=
        add_le_add (mul_le_mul_of_nonneg_left (hbound _).1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (hbound _).2 (abs_nonneg _))
      _ = (‖ℓ‖ + |a|) * A * Real.exp (-|a * x|) := by ring
      _ ≤ _ := by
        dsimp [M]
        gcongr
        linarith


/-- The one-sided limits at a lattice point give the midpoint multiplied by the character value. -/
private theorem mellinTwist_tendsto_lattice {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f)
    {a : ℝ} (ha : a ≠ 0) (c : Circle) {ℓ : ℂ} (hℓ : Complex.exp ℓ = (c : ℂ)) (n : ℤ) :
    let g (x : ℝ) := Complex.exp (ℓ * (x : ℂ)) * f (a * x)
    ∃ u v : ℂ, Tendsto (fun x : ℝ ↦ g (x + n)) (𝓝[>] 0) (𝓝 u) ∧
      Tendsto (fun x : ℝ ↦ g (-x + n)) (𝓝[>] 0) (𝓝 v) ∧
      (u + v) / 2 = (c : ℂ) ^ n * mellinJumpMidpoint f ((n : ℝ) * a) := by
  dsimp only
  have hlimits (x : ℝ) : ∃ l r : ℂ, Tendsto f (𝓝[<] x) (𝓝 l) ∧ Tendsto f (𝓝[>] x) (𝓝 r) := by
    obtain ⟨S, hS, hlim⟩ := hf.1
    by_cases hx : x ∈ S
    · obtain ⟨⟨l, hl⟩, ⟨r, hr⟩⟩ := hlim 0 x hx
      exact ⟨l, r, by rwa [iteratedDeriv_zero] at hl, by rwa [iteratedDeriv_zero] at hr⟩
    · have h := hS.continuousOn.continuousAt (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hx)
      exact ⟨f x, f x, h.tendsto.mono_left nhdsWithin_le_nhds, h.tendsto.mono_left nhdsWithin_le_nhds⟩
  obtain ⟨l, r, hl, hr⟩ := hlimits ((n : ℝ) * a)
  let w (x : ℝ) := Complex.exp (ℓ * (x : ℂ))
  have h₀ : Tendsto (fun x : ℝ ↦ x) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hw : Continuous w := by dsimp [w]; fun_prop
  have he : w (n : ℝ) = (c : ℂ) ^ n := by
    rw [show w (n : ℝ) = Complex.exp ((n : ℂ) * ℓ) by
      simp [w, mul_comm], Complex.exp_int_mul, hℓ]
  have hright : Tendsto (fun x : ℝ ↦ w (x + n)) (𝓝[>] 0) (𝓝 ((c : ℂ) ^ n)) := by
    rw [← he]
    exact (hw.tendsto (n : ℝ)).comp (by simpa only [zero_add] using h₀.add_const (n : ℝ))
  have hleft : Tendsto (fun x : ℝ ↦ w (-x + n)) (𝓝[>] 0) (𝓝 ((c : ℂ) ^ n)) := by
    rw [← he]
    exact (hw.tendsto (n : ℝ)).comp
      (by simpa only [neg_zero, zero_add] using h₀.neg.add_const (n : ℝ))
  have hrescale (d : ℝ) :
      Tendsto (fun x : ℝ ↦ (n : ℝ) * a + d * x) (𝓝[>] 0) (𝓝 ((n : ℝ) * a)) := by
    simpa only [mul_zero, add_zero] using (h₀.const_mul d).const_add ((n : ℝ) * a)
  have hrescale_pos (d : ℝ) (hd : 0 < d) :
      Tendsto (fun x : ℝ ↦ (n : ℝ) * a + d * x) (𝓝[>] 0) (𝓝[>] ((n : ℝ) * a)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrescale d, by
      filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with x hx
      exact lt_add_of_pos_right _ (mul_pos hd hx)⟩
  have hrescale_neg (d : ℝ) (hd : d < 0) :
      Tendsto (fun x : ℝ ↦ (n : ℝ) * a + d * x) (𝓝[>] 0) (𝓝[<] ((n : ℝ) * a)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrescale d, by
      filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with x hx
      exact add_lt_of_neg_right _ (mul_neg_of_neg_of_pos hd hx)⟩
  have hplus (x : ℝ) : a * (x + (n : ℝ)) = (n : ℝ) * a + a * x := by ring
  have hminus (x : ℝ) : a * (-x + (n : ℝ)) = (n : ℝ) * a + (-a) * x := by ring
  rw [mellinJumpMidpoint_eq_average hl hr]
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · refine ⟨(c : ℂ) ^ n * l, (c : ℂ) ^ n * r, ?_, ?_, by ring⟩
    · simpa only [w, hplus, Function.comp_def] using hright.mul (hl.comp (hrescale_neg a ha'))
    · simpa only [w, hminus, Function.comp_def] using hleft.mul (hr.comp (hrescale_pos (-a) (by linarith)))
  · refine ⟨(c : ℂ) ^ n * r, (c : ℂ) ^ n * l, ?_, ?_, by ring⟩
    · simpa only [w, hplus, Function.comp_def] using hright.mul (hr.comp (hrescale_pos a ha'))
    · simpa only [w, hminus, Function.comp_def] using hleft.mul (hl.comp (hrescale_neg (-a) (by linarith)))

/-- Paper: Proposition B.4.1.2, p. 609. The twisted periodization is bounded on a
fundamental interval. Its even part approaches the weighted midpoint sum at least
linearly at the center of that interval. -/
private theorem mellinTwistedPeriodization_bounds {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f)
    {a : ℝ} (ha : a ≠ 0) (c : Circle) {ℓ : ℂ} (hℓ : Complex.exp ℓ = (c : ℂ)) :
    let F (x : ℝ) := ∑' n : ℤ, Complex.exp (ℓ * ((x + (n : ℝ) : ℝ) : ℂ)) * f (a * (x + n))
    let L := ∑' n : ℤ, (c : ℂ) ^ n * mellinJumpMidpoint f ((n : ℝ) * a)
    ∃ C ≥ (0 : ℝ),
      (∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ‖F x‖ ≤ C) ∧
      ∀ x ∈ Ioc (0 : ℝ) (1 / 2), ‖F x + F (-x) - 2 * L‖ ≤ C * x := by
  dsimp only
  have hunit : ℓ.re = 0 :=
    (Real.exp_eq_one_iff ℓ.re).mp (by rw [← Complex.norm_exp, hℓ, Circle.norm_coe])
  obtain ⟨S, hS, A, hA, hg, hderiv⟩ := mellinTest_twisted_deriv_bound hf ha hunit
  choose u v hu hv hmean using fun n : ℤ ↦ mellinTwist_tendsto_lattice hf ha c hℓ n
  simpa only [hmean] using periodization_bounds_of_exp_decay hS hA (abs_pos.mpr ha)
    hg hderiv hu hv

open MeasureTheory in
/-- Paper: Proposition B.4.1.2, p. 608. The symmetric frequency sums converge
to the weighted midpoint sum times the logarithmic lattice spacing. The limit
is the same for every complex logarithm of the character value on the generator.
Deviation: Uses `|log θ|` in (B.4.1.7) and takes the ordinary complex logarithm
of `χ(θ)` in its numerator. -/
theorem tendsto_mellinPoissonSum_of_piecewiseSmooth
    {f : ℝ → ℂ} (hf : IsPiecewiseSmoothMellinTest f) {θ : ℝ}
    (hθ : 0 < θ) (hθ₁ : θ ≠ 1) (c : Circle) (ℓ : ℂ) (hℓ : Complex.exp ℓ = (c : ℂ)) :
    Tendsto (fun N : ℕ ↦
      ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        logMellin f ((ℓ + twoPiI * (m : ℂ)) / (Real.log θ : ℂ))) atTop
      (𝓝 (((|Real.log θ| : ℝ) : ℂ) *
        ∑' m : ℤ, (c : ℂ) ^ m * mellinJumpMidpoint f ((m : ℝ) * Real.log θ))) := by
  let a := Real.log θ
  have ha : a ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hθ hθ₁
  let w (x : ℝ) := Complex.exp (ℓ * (x : ℂ))
  let g (x : ℝ) := w x * f (a * x)
  let F (x : ℝ) := ∑' n : ℤ, g (x + n)
  let L := ∑' n : ℤ, (c : ℂ) ^ n * mellinJumpMidpoint f ((n : ℝ) * a)
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hw_norm (x : ℝ) : ‖w x‖ = 1 := by
    have hre : ℓ.re = 0 :=
      (Real.exp_eq_one_iff ℓ.re).mp (by rw [← Complex.norm_exp, hℓ, Circle.norm_coe])
    simp [w, Complex.norm_exp, Complex.mul_re, hre]
  have hfi : Integrable f := by
    apply (integrableOn_comp_log_Ioi_zero f).mp
    simpa [MellinConvergent, Complex.cpow_neg_one, Complex.real_smul] using
      mellinConvergent_of_piecewiseSmoothMellinTest hf 0
  have hg : Integrable g :=
    (hfi.comp_mul_left' ha).bdd_mul hw.aestronglyMeasurable (Eventually.of_forall fun x ↦ (hw_norm x).le)
  have hmeas : Measurable f := by
    obtain ⟨⟨S, hS, -⟩, -⟩ := hf
    exact hS.continuousOn.measurable_of_countable_compl (by simpa using S.finite_toSet.countable)
  have hgm : Measurable g :=
    hw.measurable.mul (hmeas.comp (measurable_const.mul measurable_id))
  have hFm : Measurable F :=
    Measurable.tsum (fun n : ℤ ↦ hgm.comp (measurable_id.add_const (n : ℝ)))
  obtain ⟨C, hC, hFbound, hresidual⟩ := mellinTwistedPeriodization_bounds hf ha c hℓ
  change ∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ‖F x‖ ≤ C at hFbound
  change ∀ x ∈ Ioc (0 : ℝ) (1 / 2), ‖F x + F (-x) - 2 * L‖ ≤ C * x at hresidual
  have hF : IntervalIntegrable F volume (-(1 / 2)) (1 / 2) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
    refine (integrable_const C).mono' hFm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hFbound x (Ioc_subset_Icc_self hx)
  have hquot : IntegrableOn
      (fun x : ℝ ↦ (F x + F (-x) - 2 * L) / (Complex.exp (twoPiI * (x : ℂ)) - 1))
      (Ioc 0 (1 / 2)) := by
    have hm : Measurable (fun x : ℝ ↦
        (F x + F (-x) - 2 * L) / (Complex.exp (twoPiI * (x : ℂ)) - 1)) := by
      fun_prop
    refine (integrable_const C).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hx' : 0 < x := hx.1
    have hs : 2 * x ≤ Real.sin (Real.pi * x) := by
      have hs₀ := Real.mul_le_sin (mul_nonneg Real.pi_pos.le hx'.le)
        (by nlinarith only [mul_le_mul_of_nonneg_left hx.2 Real.pi_pos.le] :
          Real.pi * x ≤ Real.pi / 2)
      have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
      rwa [heq] at hs₀
    have hnorm : 4 * x ≤ ‖Complex.exp (twoPiI * (x : ℂ)) - 1‖ := by
      have heq : twoPiI * (x : ℂ) = Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq, Complex.norm_exp_I_mul_ofReal_sub_one,
        show 2 * Real.pi * x / 2 = Real.pi * x by ring]
      exact (by linarith : 4 * x ≤ 2 * Real.sin (Real.pi * x)).trans (le_abs_self _)
    rw [norm_div, div_le_iff₀ ((by positivity : 0 < 4 * x).trans_le hnorm)]
    exact (hresidual x hx).trans (mul_le_mul_of_nonneg_left (by linarith) hC |>.trans
      (mul_le_mul_of_nonneg_left hnorm hC))
  have hlim := (tendsto_symmetric_fourier_integrals_of_integrable_quotient hF hquot).const_mul
    ((|a| : ℝ) : ℂ)
  convert hlim using 1
  ext N
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  change mellin (fun t ↦ f (Real.log t)) ((ℓ + twoPiI * (m : ℂ)) / (a : ℂ)) = _
  rw [logMellin_eq_mul_integral_twist f ha ℓ m]
  congr 1
  exact (integral_periodization_mul_exp_int hg m).symm

end Sol_ExplicitFormula_poisson_summation_mellin_of_piecewise_smooth


theorem solution
    (g : ℝ → ℂ) (S : Finset ℝ)
    (hsmooth : ContDiffOn ℝ ∞ g (S : Set ℝ)ᶜ)
    (hlim : ∀ (j : ℕ) (x : ℝ), x ∈ S →
      (∃ l : ℂ, Tendsto (iteratedDeriv j g) (𝓝[<] x) (𝓝 l)) ∧
      (∃ r : ℂ, Tendsto (iteratedDeriv j g) (𝓝[>] x) (𝓝 r)))
    (hdecay : ∀ N : ℕ, ∃ C > (0 : ℝ), ∃ T > (0 : ℝ), ∀ x : ℝ, T < |x| →
      ‖g x‖ < C * Real.exp (-(N : ℝ) * |x|) ∧ ‖deriv g x‖ < C * Real.exp (-(N : ℝ) * |x|))
    (θ : ℝ) (hθ : 0 < θ) (hθ₁ : θ ≠ 1) (c : Circle) (ℓ : ℂ) (hℓ : Complex.exp ℓ = (c : ℂ)) :
    Summable (fun m : ℤ => (c : ℂ) ^ m *
      ((limUnder (𝓝[<] ((m : ℝ) * Real.log θ)) g +
        limUnder (𝓝[>] ((m : ℝ) * Real.log θ)) g) / 2)) ∧
    Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        mellin (fun t : ℝ => g (Real.log t)) ((ℓ + 2 * π * Complex.I * m) / Real.log θ))
      atTop
      (𝓝 ((|Real.log θ| : ℝ) * ∑' m : ℤ, (c : ℂ) ^ m *
        ((limUnder (𝓝[<] ((m : ℝ) * Real.log θ)) g +
          limUnder (𝓝[>] ((m : ℝ) * Real.log θ)) g) / 2))) := by
  have hf : Sol_ExplicitFormula_poisson_summation_mellin_of_piecewise_smooth.IsPiecewiseSmoothMellinTest g :=
    ⟨⟨S, hsmooth, hlim⟩, hdecay⟩
  exact ⟨Sol_ExplicitFormula_poisson_summation_mellin_of_piecewise_smooth.summable_mellinJumpMidpoint_lattice
      hf hθ hθ₁ c,
    Sol_ExplicitFormula_poisson_summation_mellin_of_piecewise_smooth.tendsto_mellinPoissonSum_of_piecewiseSmooth
      hf hθ hθ₁ c ℓ hℓ⟩
