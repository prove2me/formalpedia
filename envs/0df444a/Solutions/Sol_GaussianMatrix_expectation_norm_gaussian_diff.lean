-- Prove2me | solution 1 for GaussianMatrix.expectation_norm_gaussian_diff
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T07:39:37.352888+00:00
-- url     : https://prove2.me/submissions/a7564fe6-4ae4-45a8-a53a-799679e74274

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

open Real Set

/-- The product of `m` standard Gaussians has density `∏ᵢ φ(xᵢ)` w.r.t. Lebesgue measure. -/
lemma en_pi_gauss (m : ℕ) :
    Measure.pi (fun _ : Fin m => gaussianReal 0 1)
      = volume.withDensity
          (fun x : Fin m → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  refine Measure.pi_eq (μ := fun _ : Fin m => gaussianReal 0 1) fun s hs => ?_
  have hS : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  have hind : ∀ x : Fin m → ℝ,
      (Set.univ.pi s).indicator (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) x
        = ENNReal.ofReal (∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i)) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
      simp
  simp_rw [hind]
  have hint : Integrable (fun x : Fin m → ℝ => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i))
      volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun i => (s i).indicator (gaussianPDFReal 0 1))
      (fun i => (integrable_gaussianPDFReal 0 1).indicator (hs i))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ =>
      Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  rw [integral_fintype_prod_volume_eq_prod, ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg fun y =>
      Set.indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero, integral_indicator (hs i)]

lemma en_prod_pdf {m : ℕ} (x : Fin m → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (x i)
      = (Real.sqrt (2 * π))⁻¹ ^ m * Real.exp (-(∑ i, x i ^ 2) / 2) := by
  simp only [gaussianPDFReal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  congr 2
  · simp
  · simp only [sub_zero, NNReal.coe_one, mul_one, neg_div]
    rw [Finset.sum_neg_distrib, Finset.sum_div]

lemma en_sum_sq_ofLp {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    ∑ i, (WithLp.ofLp y) i ^ 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

/-- Polar coordinates for a radial function of a standard Gaussian vector. -/
lemma en_radial (m : ℕ) (hm : 1 ≤ m) (φ : ℝ → ℝ) :
    ∫ x, φ (Real.sqrt (∑ i, x i ^ 2)) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = m * (volume : Measure (EuclideanSpace ℝ (Fin m))).real (Metric.ball 0 1)
        * ((Real.sqrt (2 * π))⁻¹ ^ m
          * ∫ y in Ioi (0 : ℝ), y ^ (m - 1) * (Real.exp (-y ^ 2 / 2) * φ y)) := by
  rw [en_pi_gauss, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _),
    smul_eq_mul, en_prod_pdf]
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).integral_comp']
  simp only [MeasurableEquiv.toLp_symm_apply]
  simp_rw [en_sum_sq_ofLp, Real.sqrt_sq (norm_nonneg _)]
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin m)) := inferInstance
  have := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin m)))
    (fun r => (Real.sqrt (2 * π))⁻¹ ^ m * Real.exp (-r ^ 2 / 2) * φ r)
  rw [this, finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
  simp_rw [smul_eq_mul]
  have e : ∀ y : ℝ, y ^ (m - 1) * ((Real.sqrt (2 * π))⁻¹ ^ m * Real.exp (-y ^ 2 / 2) * φ y)
      = (Real.sqrt (2 * π))⁻¹ ^ m * (y ^ (m - 1) * (Real.exp (-y ^ 2 / 2) * φ y)) := fun y => by
    ring
  simp_rw [e]
  rw [integral_const_mul]
  ring


/-- `J k = ∫₀^∞ y^k e^{-y²/2} dy`. -/
noncomputable def enJ (k : ℕ) : ℝ := ∫ y in Ioi (0 : ℝ), y ^ k * Real.exp (-y ^ 2 / 2)

lemma enJ_eq (k : ℕ) :
    enJ k = (1 / 2 : ℝ) ^ (-((k : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((k : ℝ) + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (k : ℝ)) (b := 1 / 2)
    (by norm_num) (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith) (by norm_num)
  rw [← h, enJ]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [Real.rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  congr 2
  ring

lemma enJ_pos (k : ℕ) : 0 < enJ k := by
  rw [enJ_eq]
  have : 0 < ((k : ℝ) + 1) / 2 := by positivity
  have := Real.Gamma_pos_of_pos this
  positivity

lemma enJ_rec (k : ℕ) : enJ (k + 2) = (k + 1) * enJ k := by
  rw [enJ_eq, enJ_eq]
  push_cast
  have hG : Real.Gamma (((k : ℝ) + 2 + 1) / 2) = ((k : ℝ) + 1) / 2 * Real.Gamma (((k : ℝ) + 1) / 2) := by
    rw [show ((k : ℝ) + 2 + 1) / 2 = ((k : ℝ) + 1) / 2 + 1 by ring]
    exact Real.Gamma_add_one (by positivity)
  have hp : (1 / 2 : ℝ) ^ (-((k : ℝ) + 2 + 1) / 2)
      = (1 / 2 : ℝ) ^ (-((k : ℝ) + 1) / 2) * 2 := by
    rw [show -((k : ℝ) + 2 + 1) / 2 = -((k : ℝ) + 1) / 2 + (-1) by ring,
      Real.rpow_add (by norm_num), Real.rpow_neg_one]
    norm_num
  rw [hG, hp]
  ring

/-- `𝔼‖g_m‖ = J m / J (m - 1)` for a standard Gaussian vector `g_m ∈ ℝ^m`, `m ≥ 1`. -/
lemma en_norm_eq (m : ℕ) (hm : 1 ≤ m) :
    ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = enJ m / enJ (m - 1) := by
  have h1 := en_radial m hm (fun _ => 1)
  have h2 := en_radial m hm (fun y => y)
  simp only [integral_const, smul_eq_mul, mul_one] at h1
  rw [measureReal_def, measure_univ, ENNReal.toReal_one] at h1
  have e1 : ∫ y in Ioi (0 : ℝ), y ^ (m - 1) * Real.exp (-y ^ 2 / 2) = enJ (m - 1) := rfl
  have e2 : ∫ y in Ioi (0 : ℝ), y ^ (m - 1) * (Real.exp (-y ^ 2 / 2) * y) = enJ m := by
    rw [enJ]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    conv_rhs => rw [show m = m - 1 + 1 by omega, pow_succ]
    ring
  rw [e1] at h1
  rw [h2, e2]
  have hJ := enJ_pos (m - 1)
  rw [eq_div_iff hJ.ne']
  have : (m : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin m))).real (Metric.ball 0 1)
        * ((Real.sqrt (2 * π))⁻¹ ^ m * enJ m) * enJ (m - 1)
      = enJ m * ((m : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin m))).real (Metric.ball 0 1)
        * ((Real.sqrt (2 * π))⁻¹ ^ m * enJ (m - 1))) := by ring
  rw [this, ← h1, mul_one]


/-- Log-convexity of `Γ` gives `J (k+1)² ≤ J k · J (k+2)`. -/
lemma enJ_logconvex (k : ℕ) : enJ (k + 1) ^ 2 ≤ enJ k * enJ (k + 2) := by
  rw [enJ_eq, enJ_eq, enJ_eq]
  push_cast
  set s : ℝ := ((k : ℝ) + 1) / 2 with hs
  have hs0 : 0 < s := by positivity
  have hG := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := s) (t := s + 1)
    (a := 1 / 2) (b := 1 / 2) hs0 (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have e1 : (1 / 2 : ℝ) * s + 1 / 2 * (s + 1) = ((k : ℝ) + 1 + 1) / 2 := by rw [hs]; ring
  have e3 : ((k : ℝ) + 2 + 1) / 2 = s + 1 := by rw [hs]; ring
  rw [e1] at hG
  rw [e3]
  have hGs := Real.Gamma_pos_of_pos hs0
  have hGt := Real.Gamma_pos_of_pos (show 0 < s + 1 by linarith)
  have hGm := Real.Gamma_pos_of_pos (show 0 < ((k : ℝ) + 1 + 1) / 2 by positivity)
  have hG2 : Real.Gamma (((k : ℝ) + 1 + 1) / 2) ^ 2 ≤ Real.Gamma s * Real.Gamma (s + 1) := by
    have hsq : (Real.Gamma s ^ (1 / 2 : ℝ) * Real.Gamma (s + 1) ^ (1 / 2 : ℝ)) ^ 2
        = Real.Gamma s * Real.Gamma (s + 1) := by
      rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (Real.Gamma (s + 1) ^ (1 / 2 : ℝ)),
        ← Real.rpow_mul hGs.le, ← Real.rpow_mul hGt.le]
      norm_num
    rw [← hsq]
    exact pow_le_pow_left₀ hGm.le hG 2
  have hP : ((1 / 2 : ℝ) ^ (-((k : ℝ) + 1 + 1) / 2)) ^ 2
      = (1 / 2 : ℝ) ^ (-((k : ℝ) + 1) / 2) * (1 / 2 : ℝ) ^ (-((k : ℝ) + 2 + 1) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  have hP0 : 0 < (1 / 2 : ℝ) ^ (-((k : ℝ) + 1) / 2) * (1 / 2 : ℝ) ^ (-((k : ℝ) + 2 + 1) / 2) := by
    positivity
  calc ((1 / 2 : ℝ) ^ (-((k : ℝ) + 1 + 1) / 2) * (1 / 2) * Real.Gamma (((k : ℝ) + 1 + 1) / 2)) ^ 2
      = ((1 / 2 : ℝ) ^ (-((k : ℝ) + 1 + 1) / 2)) ^ 2 * (1 / 4)
          * Real.Gamma (((k : ℝ) + 1 + 1) / 2) ^ 2 := by ring
    _ ≤ ((1 / 2 : ℝ) ^ (-((k : ℝ) + 1 + 1) / 2)) ^ 2 * (1 / 4)
          * (Real.Gamma s * Real.Gamma (s + 1)) := by
        apply mul_le_mul_of_nonneg_left hG2; positivity
    _ = (1 / 2 : ℝ) ^ (-((k : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma s *
          ((1 / 2 : ℝ) ^ (-((k : ℝ) + 2 + 1) / 2) * (1 / 2) * Real.Gamma (s + 1)) := by
        rw [hP]; ring


/-! ### The sequence argument -/
/-- Comparison sequence `B m = m - 1/2 + 3/(20 m)`. -/
noncomputable def enB (m : ℝ) : ℝ := m - 1 / 2 + 3 / (20 * m)

lemma enB_pos {m : ℝ} (hm : 1 ≤ m) : 0 < enB m := by
  unfold enB
  have : 0 < 3 / (20 * m) := by positivity
  linarith

lemma enB_mono_step {m : ℝ} (hm : 1 ≤ m) : m ^ 2 * enB (m + 2) ≤ (m + 1) ^ 2 * enB m := by
  unfold enB
  have hm0 : 0 < m := by linarith
  rw [← sub_nonneg]
  have e : (m + 1) ^ 2 * (m - 1 / 2 + 3 / (20 * m)) - m ^ 2 * (m + 2 - 1 / 2 + 3 / (20 * (m + 2)))
      = (2 * m ^ 2 - 5 * m + 6) / (20 * m * (m + 2)) := by
    field_simp
    ring
  rw [e]
  apply div_nonneg _ (by positivity)
  nlinarith [sq_nonneg (m - 5 / 4)]

lemma enB_le_div {M : ℝ} (hM : 1 ≤ M) : M / enB M ≤ 1 + 1 / M := by
  have hB := enB_pos hM
  rw [div_le_iff₀ hB]
  unfold enB
  have hM0 : 0 < M := by linarith
  have e : (1 + 1 / M) * (M - 1 / 2 + 3 / (20 * M)) - M
      = (1 / 2) - 1 / (2 * M) + 3 / (20 * M) + 3 / (20 * M ^ 2) := by
    field_simp; ring
  have h1 : 1 / (2 * M) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have : 0 ≤ 3 / (20 * M) := by positivity
  have : 0 ≤ 3 / (20 * M ^ 2) := by positivity
  nlinarith

/-- Abstract sequence argument: if `a m · a (m+1) = m`, `a m > 0` and `a m² ≤ m` for `m ≥ 1`,
then `a m² ≤ m - 1/2 + 3/(20m)`. -/
lemma en_seq_sq_le (a : ℕ → ℝ) (hpos : ∀ m, 1 ≤ m → 0 < a m)
    (hrec : ∀ m, 1 ≤ m → a m * a (m + 1) = m) (hsq : ∀ m, 1 ≤ m → a m ^ 2 ≤ m)
    (m : ℕ) (hm : 1 ≤ m) : a m ^ 2 ≤ enB m := by
  have hstep : ∀ k, 1 ≤ k → a (k + 2) = ((k : ℝ) + 1) / k * a k := by
    intro k hk
    have h1 := hrec k hk
    have h2 := hrec (k + 1) (by omega)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have ha1 := hpos (k + 1) (by omega)
    push_cast at h2
    rw [show k + 1 + 1 = k + 2 by ring] at h2
    field_simp
    nlinarith
  -- ratio `ρ k = a k² / B k` is nondecreasing along steps of two
  have hmono : ∀ k, 1 ≤ k → a k ^ 2 / enB k ≤ a (k + 2) ^ 2 / enB ((k + 2 : ℕ)) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    have hB := enB_pos hk1
    have hB2 := enB_pos (show (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) by push_cast; linarith)
    rw [hstep k hk, div_le_div_iff₀ hB hB2]
    have hms := enB_mono_step hk1
    push_cast
    have e : (((k : ℝ) + 1) / k * a k) ^ 2 = ((k : ℝ) + 1) ^ 2 * a k ^ 2 / k ^ 2 := by
      field_simp
    rw [e]
    rw [show ((k : ℝ) + 1) ^ 2 * a k ^ 2 / k ^ 2 * enB k
        = a k ^ 2 * (((k : ℝ) + 1) ^ 2 * enB k) / k ^ 2 by ring]
    rw [le_div_iff₀ (by positivity)]
    have : a k ^ 2 * (k ^ 2 * enB (k + 2)) ≤ a k ^ 2 * ((k + 1) ^ 2 * enB k) :=
      mul_le_mul_of_nonneg_left hms (sq_nonneg _)
    nlinarith
  have hiter : ∀ j : ℕ, a m ^ 2 / enB m ≤ a (m + 2 * j) ^ 2 / enB ((m + 2 * j : ℕ)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine ih.trans ?_
      have := hmono (m + 2 * j) (by omega)
      rwa [show m + 2 * j + 2 = m + 2 * (j + 1) by ring] at this
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hB := enB_pos hm1
  by_contra hcon
  push Not at hcon
  set ρ := a m ^ 2 / enB m with hρ
  have hρ1 : 1 < ρ := by rw [hρ, lt_div_iff₀ hB]; linarith
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / (ρ - 1))
  set M : ℕ := m + 2 * j with hM
  have hM1 : (1 : ℝ) ≤ M := by rw [hM]; push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hBM := enB_pos hM1
  have h1 := hiter j
  rw [← hM] at h1
  have h2 : a M ^ 2 / enB M ≤ M / enB M :=
    div_le_div_of_nonneg_right (hsq M (by omega)) hBM.le
  have h3 := enB_le_div hM1
  have hj0 : (0 : ℝ) < j := lt_trans (by positivity) hj
  have hjM : (j : ℝ) ≤ M := by rw [hM]; push_cast; linarith
  have h4 : 1 / (M : ℝ) < ρ - 1 := by
    have : 1 / (M : ℝ) ≤ 1 / j := one_div_le_one_div_of_le hj0 hjM
    have : 1 / (j : ℝ) < ρ - 1 := by
      rw [div_lt_iff₀ hj0]
      rw [div_lt_iff₀ (by linarith)] at hj
      linarith
    linarith
  linarith

/-- `√(m(m+1)) ≥ m + 1/2 - 1/(8m)` for `m ≥ 1`. -/
lemma en_sqrt_mul_ge {m : ℝ} (hm : 1 ≤ m) :
    m + 1 / 2 - 1 / (8 * m) ≤ Real.sqrt m * Real.sqrt (m + 1) := by
  rw [← Real.sqrt_mul (by linarith)]
  apply Real.le_sqrt_of_sq_le
  have hm0 : 0 < m := by linarith
  have e : (m + 1 / 2 - 1 / (8 * m)) ^ 2 = m * (m + 1) - 1 / (8 * m) + 1 / (64 * m ^ 2) := by
    field_simp; ring
  rw [e]
  have : 1 / (64 * m ^ 2) ≤ 1 / (8 * m) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  linarith

/-- One step: if `0 < a ≤ √(B m)` and `a · b = m` then `b - a ≥ √(m+1) - √m`. -/
lemma en_step {m a b : ℝ} (hm : 1 ≤ m) (ha : 0 < a) (hab : a * b = m) (hB : a ^ 2 ≤ enB m) :
    Real.sqrt (m + 1) - Real.sqrt m ≤ b - a := by
  have hm0 : 0 < m := by linarith
  have hb : b = m / a := by field_simp; linarith
  rw [hb]
  set s := Real.sqrt m with hs
  set t := Real.sqrt (m + 1) with ht
  have hs0 : 0 < s := Real.sqrt_pos.2 hm0
  have ht0 : 0 < t := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = m := Real.sq_sqrt hm0.le
  have ht2 : t ^ 2 = m + 1 := Real.sq_sqrt (by linarith)
  have hst := en_sqrt_mul_ge hm
  rw [← hs, ← ht] at hst
  have hd : t - s = 1 / (t + s) := by
    field_simp
    nlinarith
  have hts : 0 < t + s := by linarith
  have hc : 0 < 1 / 2 - 3 / (20 * m) := by
    have : 3 / (20 * m) ≤ 3 / 20 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hma : 1 / 2 - 3 / (20 * m) ≤ m - a ^ 2 := by unfold enB at hB; linarith
  have hsq : 4 * m + 2 - 1 / (4 * m) ≤ (t + s) ^ 2 := by
    have : (t + s) ^ 2 = t ^ 2 + s ^ 2 + 2 * (s * t) := by ring
    rw [this, ht2, hs2]
    have : 2 * (m + 1 / 2 - 1 / (8 * m)) = 2 * m + 1 - 1 / (4 * m) := by field_simp; ring
    linarith
  have hpoly : enB m ≤ (1 / 2 - 3 / (20 * m)) ^ 2 * (4 * m + 2 - 1 / (4 * m)) := by
    unfold enB
    rw [← sub_nonneg]
    have e : (1 / 2 - 3 / (20 * m)) ^ 2 * (4 * m + 2 - 1 / (4 * m)) - (m - 1 / 2 + 3 / (20 * m))
        = (640 * m ^ 3 - 676 * m ^ 2 + 132 * m - 9) / (1600 * m ^ 3) := by
      field_simp; ring
    rw [e]
    apply div_nonneg _ (by positivity)
    nlinarith [sq_nonneg (m - 1), mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 hm)]
  have h5 : a ^ 2 ≤ ((1 / 2 - 3 / (20 * m)) * (t + s)) ^ 2 := by
    rw [mul_pow]
    refine hB.trans (hpoly.trans ?_)
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
  have h6 : a ≤ (1 / 2 - 3 / (20 * m)) * (t + s) :=
    (pow_le_pow_iff_left₀ ha.le (by positivity) (by norm_num)).1 h5
  have hkey : a ≤ (m - a ^ 2) * (t + s) :=
    h6.trans (mul_le_mul_of_nonneg_right hma hts.le)
  have e2 : m / a - a = (m - a ^ 2) / a := by field_simp
  rw [hd, e2, div_le_div_iff₀ hts ha]
  linarith

/-- Telescoping: `a N - a n ≥ √N - √n` for `N ≥ n ≥ 1`. -/
lemma en_seq_diff (a : ℕ → ℝ) (hpos : ∀ m, 1 ≤ m → 0 < a m)
    (hrec : ∀ m, 1 ≤ m → a m * a (m + 1) = m) (hsq : ∀ m, 1 ≤ m → a m ^ 2 ≤ m)
    {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    Real.sqrt N - Real.sqrt n ≤ a N - a n := by
  induction N, hnN using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hk1 : 1 ≤ k := le_trans hn hk
    have hst := en_step (m := (k : ℝ)) (by exact_mod_cast hk1) (hpos k hk1) (hrec k hk1)
      (en_seq_sq_le a hpos hrec hsq k hk1)
    push_cast
    linarith

/-- The four properties of `a m = 𝔼‖g_m‖` used by the sequence argument. -/
lemma en_props :
    let a : ℕ → ℝ := fun m =>
      ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
    (∀ m, 1 ≤ m → 0 < a m) ∧ (∀ m, 1 ≤ m → a m * a (m + 1) = m) ∧
      (∀ m, 1 ≤ m → a m ^ 2 ≤ m) := by
  intro a
  have ha : ∀ m, 1 ≤ m → a m = enJ m / enJ (m - 1) := fun m hm => en_norm_eq m hm
  have hrec : ∀ m, 1 ≤ m → a m * a (m + 1) = m := by
    intro m hm
    rw [ha m hm, ha (m + 1) (by omega), Nat.add_sub_cancel]
    have h := enJ_rec (m - 1)
    rw [show m - 1 + 2 = m + 1 by omega, Nat.cast_sub hm] at h
    have h0 := enJ_pos (m - 1)
    have h1 := enJ_pos m
    rw [h]
    field_simp
    push_cast
    ring
  have hpos : ∀ m, 1 ≤ m → 0 < a m := fun m hm => by
    rw [ha m hm]; exact div_pos (enJ_pos _) (enJ_pos _)
  refine ⟨hpos, hrec, fun m hm => ?_⟩
  have hmono : a m ≤ a (m + 1) := by
    rw [ha m hm, ha (m + 1) (by omega), Nat.add_sub_cancel,
      div_le_div_iff₀ (enJ_pos _) (enJ_pos _)]
    have h := enJ_logconvex (m - 1)
    rw [show m - 1 + 1 = m by omega, show m - 1 + 2 = m + 1 by omega] at h
    nlinarith
  have := hrec m hm
  have := hpos m hm
  nlinarith

end GaussianMatrix

open GaussianMatrix

theorem solution {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    Real.sqrt N - Real.sqrt n ≤
      ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        - ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  obtain ⟨hpos, hrec, hsq⟩ := en_props
  exact en_seq_diff (fun m =>
      ∫ x, Real.sqrt (∑ i, x i ^ 2) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1))
    hpos hrec hsq hn hnN
