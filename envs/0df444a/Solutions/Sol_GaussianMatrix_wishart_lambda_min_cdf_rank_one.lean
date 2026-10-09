-- Prove2me | solution 1 for GaussianMatrix.wishart_lambda_min_cdf_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:32:23.002711+00:00
-- url     : https://prove2.me/submissions/b8c0567b-84b2-43af-8d10-1855ab9dd9a8

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
open Real Set

/-- The product of `m` standard Gaussians has density `∏ᵢ φ(xᵢ)` w.r.t. Lebesgue measure. -/
lemma r1_pi_gauss (m : ℕ) :
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

lemma r1_prod_pdf {m : ℕ} (x : Fin m → ℝ) :
    ∏ i, gaussianPDFReal 0 1 (x i)
      = (Real.sqrt (2 * π))⁻¹ ^ m * Real.exp (-(∑ i, x i ^ 2) / 2) := by
  simp only [gaussianPDFReal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← Real.exp_sum]
  congr 2
  · simp
  · simp only [sub_zero, NNReal.coe_one, mul_one, neg_div]
    rw [Finset.sum_neg_distrib, Finset.sum_div]

lemma r1_sum_sq_ofLp {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    ∑ i, (WithLp.ofLp y) i ^ 2 = ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

/-- Polar coordinates for a radial function of a standard Gaussian vector. -/
lemma r1_radial (m : ℕ) (hm : 1 ≤ m) (φ : ℝ → ℝ) :
    ∫ x, φ (Real.sqrt (∑ i, x i ^ 2)) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1)
      = m * (volume : Measure (EuclideanSpace ℝ (Fin m))).real (Metric.ball 0 1)
        * ((Real.sqrt (2 * π))⁻¹ ^ m
          * ∫ y in Ioi (0 : ℝ), y ^ (m - 1) * (Real.exp (-y ^ 2 / 2) * φ y)) := by
  rw [r1_pi_gauss, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 _),
    smul_eq_mul, r1_prod_pdf]
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).integral_comp']
  simp only [MeasurableEquiv.toLp_symm_apply]
  simp_rw [r1_sum_sq_ofLp, Real.sqrt_sq (norm_nonneg _)]
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
noncomputable def r1J (k : ℕ) : ℝ := ∫ y in Ioi (0 : ℝ), y ^ k * Real.exp (-y ^ 2 / 2)

lemma r1J_eq (k : ℕ) :
    r1J k = (1 / 2 : ℝ) ^ (-((k : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((k : ℝ) + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (k : ℝ)) (b := 1 / 2)
    (by norm_num) (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith) (by norm_num)
  rw [← h, r1J]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [Real.rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  congr 2
  ring


lemma r1_sMin_sq {k : ℕ} (G : Fin 1 → Fin k → ℝ) :
    sMin (Matrix.of G)ᵀ ^ 2 = ∑ j, G 0 j ^ 2 := by
  have hconst : ∀ x : {x : Fin 1 → ℝ // x ⬝ᵥ x = 1},
      Real.sqrt (((Matrix.of G)ᵀ *ᵥ x.1) ⬝ᵥ ((Matrix.of G)ᵀ *ᵥ x.1))
        = Real.sqrt (∑ j, G 0 j ^ 2) := by
    rintro ⟨x, hx⟩
    congr 1
    have hx0 : x 0 ^ 2 = 1 := by
      simpa [dotProduct, Fin.sum_univ_one, sq] using hx
    simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.of_apply,
      Fin.sum_univ_one]
    calc ∑ j, G 0 j * x 0 * (G 0 j * x 0) = ∑ j, G 0 j ^ 2 * x 0 ^ 2 :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, G 0 j ^ 2 := by simp [hx0]
  have hne : Nonempty {x : Fin 1 → ℝ // x ⬝ᵥ x = 1} :=
    ⟨⟨fun _ => 1, by simp [dotProduct]⟩⟩
  unfold sMin
  simp_rw [hconst]
  rw [ciInf_const, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

lemma r1_law {k : ℕ} (T : Set (Fin k → ℝ)) (hT : MeasurableSet T) :
    (gaussianMatrix 1 k) ((fun G => G 0) ⁻¹' T)
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1) T := by
  have h := measurePreserving_funUnique (Measure.pi fun _ : Fin k => gaussianReal 0 1) (Fin 1)
  unfold gaussianMatrix
  exact h.measure_preimage hT.nullMeasurableSet

/-- Change of variables `y = √λ`. -/
lemma r1_cov {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    ∫ y in Ioi (0 : ℝ), y ^ (k - 1) * (Real.exp (-y ^ 2 / 2)
        * (Iic (Real.sqrt t)).indicator (fun _ => (1 : ℝ)) y)
      = (1 / 2) * ∫ x in Ioc (0 : ℝ) t, x ^ (((k : ℝ) - 2) / 2) * Real.exp (-x / 2) := by
  have h := integral_comp_rpow_Ioi
    (fun x : ℝ => (Iic t).indicator (fun x => (1 / 2 : ℝ) * (x ^ (((k : ℝ) - 2) / 2)
      * Real.exp (-x / 2))) x) (p := 2) (by norm_num)
  have hR : (1 / 2 : ℝ) * ∫ x in Ioc (0 : ℝ) t, x ^ (((k : ℝ) - 2) / 2) * Real.exp (-x / 2)
      = ∫ y in Ioi (0 : ℝ), (Iic t).indicator (fun x => (1 / 2 : ℝ) * (x ^ (((k : ℝ) - 2) / 2)
          * Real.exp (-x / 2))) y := by
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Set.Iic_inter_Ioi, integral_const_mul]
  rw [hR, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
  simp only [smul_eq_mul]
  have hiff : y ^ (2 : ℝ) ∈ Iic t ↔ y ∈ Iic (Real.sqrt t) := by
    rw [Real.rpow_two, Set.mem_Iic, Set.mem_Iic, Real.le_sqrt hy.le]
    exact ht
  by_cases hyt : y ∈ Iic (Real.sqrt t)
  · rw [Set.indicator_of_mem hyt, Set.indicator_of_mem (hiff.2 hyt)]
    have hpow : y ^ (k - 1) = y ^ ((2 : ℝ) - 1) * (y ^ (2 : ℝ)) ^ (((k : ℝ) - 2) / 2) := by
      rw [← Real.rpow_mul hy.le, ← Real.rpow_add hy, ← Real.rpow_natCast, Nat.cast_sub hk]
      congr 1; push_cast; ring
    rw [hpow, abs_two, Real.rpow_two]
    ring
  · rw [Set.indicator_of_notMem hyt, Set.indicator_of_notMem (fun h => hyt (hiff.1 h))]
    simp

/-- Constant identity: `c(1,k) · 2^{k/2} Γ(k/2) = 1` (Legendre duplication). -/
lemma r1_const {k : ℕ} (hk : 1 ≤ k) :
    2 ^ (((k : ℝ) - 2) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
        / (Real.Gamma (1 / 2) * Real.Gamma (k : ℝ))
      * ((1 / 2 : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) + 1) / 2) * (1 / 2)
        * Real.Gamma ((((k - 1 : ℕ) : ℝ) + 1) / 2)) = 1 / 2 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : ((k - 1 : ℕ) : ℝ) + 1 = k := by rw [Nat.cast_sub hk]; push_cast; ring
  rw [hc]
  have hdup := Real.Gamma_mul_Gamma_add_half ((k : ℝ) / 2)
  rw [show (k : ℝ) / 2 + 1 / 2 = ((k : ℝ) + 1) / 2 by ring, show 2 * ((k : ℝ) / 2) = k by ring]
    at hdup
  have hhalf : (1 / 2 : ℝ) ^ (-(k : ℝ) / 2) = 2 ^ ((k : ℝ) / 2) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1; ring
  rw [hhalf, Real.Gamma_one_half_eq]
  have gk := Real.Gamma_pos_of_pos (show (0 : ℝ) < k by linarith)
  have gk2 := Real.Gamma_pos_of_pos (show (0 : ℝ) < k / 2 by linarith)
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have h2 : (2 : ℝ) ^ (((k : ℝ) - 2) / 2) * 2 ^ ((k : ℝ) / 2) * 2 ^ (1 - (k : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
      show ((k : ℝ) - 2) / 2 + k / 2 + (1 - k) = 0 by ring, Real.rpow_zero]
  rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]
  calc 2 ^ (((k : ℝ) - 2) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
        * (2 ^ ((k : ℝ) / 2) * (1 / 2) * Real.Gamma ((k : ℝ) / 2))
      = 2 ^ (((k : ℝ) - 2) / 2) * 2 ^ ((k : ℝ) / 2) * (Real.Gamma ((k : ℝ) / 2)
          * Real.Gamma (((k : ℝ) + 1) / 2)) * (1 / 2) := by ring
    _ = 2 ^ (((k : ℝ) - 2) / 2) * 2 ^ ((k : ℝ) / 2) * 2 ^ (1 - (k : ℝ))
          * (Real.sqrt π * Real.Gamma k) * (1 / 2) := by rw [hdup]; ring
    _ = 1 / 2 * (Real.sqrt π * Real.Gamma k) := by rw [h2]; ring

lemma r1_main {k : ℕ} (hk : 1 ≤ k) (t : ℝ) (ht : 0 ≤ t) :
    (gaussianMatrix 1 k) {G | sMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      = ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal
          (2 ^ (((k : ℝ) - 2) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
              / (Real.Gamma (1 / 2) * Real.Gamma (k : ℝ))
            * x ^ (((k : ℝ) - 2) / 2) * Real.exp (-x / 2)) := by
  set c : ℝ := 2 ^ (((k : ℝ) - 2) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
              / (Real.Gamma (1 / 2) * Real.Gamma (k : ℝ)) with hc
  set a : ℝ := ((k : ℝ) - 2) / 2 with ha
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha1 : -1 < a := by rw [ha]; linarith
  have hcpos : 0 ≤ c := by
    rw [hc]
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < k by linarith)
    have := Real.Gamma_pos_of_pos (show (0 : ℝ) < ((k : ℝ) + 1) / 2 by linarith)
    positivity
  set T : Set (Fin k → ℝ) := {g | ∑ j, g j ^ 2 ≤ t} with hT
  have hTm : MeasurableSet T := measurableSet_le (by fun_prop) measurable_const
  have hset : {G : Fin 1 → Fin k → ℝ | sMin (Matrix.of G)ᵀ ^ 2 ≤ t} = (fun G => G 0) ⁻¹' T := by
    ext G; simp [hT, r1_sMin_sq]
  rw [hset, r1_law T hTm]
  set ν := Measure.pi fun _ : Fin k => gaussianReal 0 1 with hν
  set φ : ℝ → ℝ := (Iic (Real.sqrt t)).indicator (fun _ => (1 : ℝ)) with hφ
  -- ν T as a radial integral
  have hνT : ν.real T = ∫ x, φ (Real.sqrt (∑ i, x i ^ 2)) ∂ν := by
    rw [← integral_indicator_one hTm]
    congr 1; ext x
    have hs : Real.sqrt (∑ i, x i ^ 2) ∈ Iic (Real.sqrt t) ↔ x ∈ T := by
      rw [Set.mem_Iic, Real.sqrt_le_sqrt_iff ht]; rfl
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx, hφ, Set.indicator_of_mem (hs.2 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, hφ, Set.indicator_of_notMem (fun h => hx (hs.1 h))]
  have h1 := r1_radial k hk (fun _ => 1)
  have h2 := r1_radial k hk φ
  simp only [integral_const, smul_eq_mul, mul_one] at h1
  rw [measureReal_def, measure_univ, ENNReal.toReal_one] at h1
  have e1 : ∫ y in Ioi (0 : ℝ), y ^ (k - 1) * Real.exp (-y ^ 2 / 2) = r1J (k - 1) := rfl
  rw [e1, r1J_eq] at h1
  rw [hφ, r1_cov hk ht] at h2
  -- the real integral I
  set I : ℝ := ∫ x in Ioc (0 : ℝ) t, x ^ a * Real.exp (-x / 2) with hI
  have hint : IntegrableOn (fun x : ℝ => x ^ a * Real.exp (-x / 2)) (Ioc 0 t) := by
    have hpow : IntegrableOn (fun x : ℝ => x ^ a) (Ioc 0 t) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1
        (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) ha1)
    refine hpow.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.1.le _)
      (Real.exp_pos _).le)]
    have h1 : 0 ≤ x ^ a := Real.rpow_nonneg hx.1.le _
    have h2 : Real.exp (-x / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [hx.1])
    nlinarith
  have hRHS : ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal (c * x ^ a * Real.exp (-x / 2))
      = ENNReal.ofReal (c * I) := by
    rw [hI, ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal]
    · simp_rw [mul_assoc]
    · exact hint.const_mul c
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg hcpos (mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.exp_pos _).le)
  rw [hRHS, ← ofReal_measureReal, hνT, h2]
  congr 1
  have hconst := r1_const hk
  rw [← hc] at hconst
  -- h1 : 1 = K * J,  hconst : c * J = 1/2
  set K := (k : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin k))).real (Metric.ball 0 1)
    * (Real.sqrt (2 * π))⁻¹ ^ k with hK
  set J := (1 / 2 : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) + 1) / 2) * (1 / 2)
        * Real.Gamma ((((k - 1 : ℕ) : ℝ) + 1) / 2) with hJ
  have h1' : 1 = K * J := by rw [h1, hK]; ring
  calc (k : ℝ) * (volume : Measure (EuclideanSpace ℝ (Fin k))).real (Metric.ball 0 1)
        * ((Real.sqrt (2 * π))⁻¹ ^ k * (1 / 2 * I))
      = K * (1 / 2) * I := by rw [hK]; ring
    _ = K * (c * J) * I := by rw [hconst]
    _ = (K * J) * c * I := by ring
    _ = c * I := by rw [← h1']; ring

end GaussianMatrix

open GaussianMatrix

theorem solution {k : ℕ} (hk : 1 ≤ k) (t : ℝ) (ht : 0 ≤ t) :
    (gaussianMatrix 1 k) {G | sMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      = ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal
          (2 ^ (((k : ℝ) - 2) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
              / (Real.Gamma (1 / 2) * Real.Gamma (k : ℝ))
            * x ^ (((k : ℝ) - 2) / 2) * Real.exp (-x / 2)) :=
  r1_main hk t ht

/-- Sanity check: the statement of `wishart_lambda_min_cdf_density_bound` (Edelman / TW (B.5))
holds verbatim in the case `r = 1`, where it is an equality (the `χ²_k` law). -/
theorem GaussianMatrix.wishart_lambda_min_cdf_density_bound_of_eq_one {r k : ℕ} (hr1 : r = 1)
    (hrk : r ≤ k) (t : ℝ) (ht : 0 < t) :
    (gaussianMatrix r k) {G | sMin (Matrix.of G)ᵀ ^ 2 ≤ t}
      ≤ ∫⁻ x in Set.Ioc 0 t, ENNReal.ofReal
          (2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
              / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))
            * x ^ (((k : ℝ) - r - 1) / 2) * Real.exp (-x / 2)) := by
  subst hr1
  rw [r1_main hrk t ht.le]
  apply le_of_eq
  congr 1; ext x; congr 1
  push_cast
  rw [show (k : ℝ) - 1 - 1 = k - 2 by ring, show (k : ℝ) - 1 + 1 = k by ring]
