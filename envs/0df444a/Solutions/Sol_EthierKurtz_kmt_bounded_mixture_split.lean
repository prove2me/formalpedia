-- Prove2me | solution 1 for EthierKurtz.kmt_bounded_mixture_split
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:37:29.26428+00:00
-- url     : https://prove2.me/submissions/5a9a37d5-d840-4182-9f0a-904ffad4efc5

import Mathlib
open MeasureTheory ProbabilityTheory

lemma S194K_int_iff {A B : Measure ℝ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {f : ℝ → ℝ} :
    Integrable f (ENNReal.ofReal p • A + ENNReal.ofReal (1 - p) • B) ↔
      Integrable f A ∧ Integrable f B := by
  rw [integrable_add_measure, integrable_smul_measure, integrable_smul_measure]
  · simp; linarith
  · simp
  · simp [hp0]
  · simp

lemma S194K_int_eq {A B : Measure ℝ} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {f : ℝ → ℝ}
    (hA : Integrable f A) (hB : Integrable f B) :
    ∫ x, f x ∂(ENNReal.ofReal p • A + ENNReal.ofReal (1 - p) • B) =
      p * ∫ x, f x ∂A + (1 - p) * ∫ x, f x ∂B := by
  rw [integral_add_measure (hA.smul_measure ENNReal.ofReal_ne_top)
    (hB.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

lemma S194K_exists_n (μ : Measure ℝ) (T : Set ℝ) (hT : μ T ≠ 0) :
    ∃ n : ℕ, μ (Set.Icc (-(n:ℝ)) n ∩ T) ≠ 0 := by
  by_contra h
  push Not at h
  apply hT
  apply measure_mono_null (t := ⋃ n : ℕ, Set.Icc (-(n:ℝ)) n ∩ T) _ (measure_iUnion_null h)
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_ge |x|
  exact Set.mem_iUnion.2 ⟨n, ⟨abs_le.1 hn, hx⟩⟩

lemma S194K_neg_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0) (hvariance : variance (fun x : ℝ => x) μ = 1) :
    μ (Set.Iio 0) ≠ 0 ∧ μ (Set.Ioi 0) ≠ 0 := by
  constructor
  · intro h
    have hae : 0 ≤ᵐ[μ] (fun x : ℝ => x) := by
      rw [Filter.EventuallyLE, ae_iff]
      convert h using 2
      ext x; simp
    have := (integral_eq_zero_iff_of_nonneg_ae hae hint).1 hmean
    rw [variance_congr this] at hvariance
    simp at hvariance
  · intro h
    have hae : 0 ≤ᵐ[μ] (fun x : ℝ => -x) := by
      rw [Filter.EventuallyLE, ae_iff]
      convert h using 2
      ext x; simp
    have := (integral_eq_zero_iff_of_nonneg_ae hae hint.neg).1 (by rw [integral_neg, hmean]; simp)
    have h2 : (fun x : ℝ => x) =ᵐ[μ] 0 := by
      filter_upwards [this] with x hx
      simpa using hx
    rw [variance_congr h2] at hvariance
    simp at hvariance

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hexp : (∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ → Integrable (fun x : ℝ => Real.exp (a * x)) μ))
    (hmean : ∫ x : ℝ, x ∂μ = 0) (hvariance : variance (fun x : ℝ => x) μ = 1) :
    ∃ (p : ℝ) (F1 F2 : Measure ℝ) (_ : IsProbabilityMeasure F1) (_ : IsProbabilityMeasure F2),
      0 < p ∧ p < 1 ∧ (∃ K : ℝ, F1 (Set.Icc (-K) K) = 1) ∧
      0 < variance (fun x : ℝ => x) F1 ∧
      μ = ENNReal.ofReal p • F1 + ENNReal.ofReal (1 - p) • F2 ∧
      (∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ → Integrable (fun x : ℝ => Real.exp (a * x)) (ENNReal.ofReal p • gaussianReal (∫ x, x ∂F1) (variance (fun x : ℝ => x) F1).toNNReal + ENNReal.ofReal (1 - p) • F2)) ∧
      ∫ x, x ∂(ENNReal.ofReal p • gaussianReal (∫ x, x ∂F1) (variance (fun x : ℝ => x) F1).toNNReal + ENNReal.ofReal (1 - p) • F2) = 0 ∧
      variance (fun x : ℝ => x) (ENNReal.ofReal p • gaussianReal (∫ x, x ∂F1) (variance (fun x : ℝ => x) F1).toNNReal + ENNReal.ofReal (1 - p) • F2) = 1 := by
  obtain ⟨a₀, ha₀, hexp⟩ := hexp
  have hpos := hexp a₀ (by rw [abs_of_pos ha₀])
  have hneg := hexp (-a₀) (by rw [abs_neg, abs_of_pos ha₀])
  have hx1 : Integrable (fun x : ℝ => x) μ := by
    simpa using integrable_pow_of_integrable_exp_mul (X := fun x : ℝ => x) ha₀.ne' hpos hneg 1
  have hx2 : Integrable (fun x : ℝ => x ^ 2) μ :=
    integrable_pow_of_integrable_exp_mul (X := fun x : ℝ => x) ha₀.ne' hpos hneg 2
  obtain ⟨hN, hP⟩ := S194K_neg_pos μ hx1 hmean hvariance
  obtain ⟨n1, hn1⟩ := S194K_exists_n μ _ hN
  obtain ⟨n2, hn2⟩ := S194K_exists_n μ _ hP
  set K : ℝ := max (n1 : ℝ) n2 with hK
  set I := Set.Icc (-K) K with hI
  have hIm : MeasurableSet I := measurableSet_Icc
  have hN' : μ (I ∩ Set.Iio 0) ≠ 0 := by
    refine fun h => hn1 (measure_mono_null ?_ h)
    exact Set.inter_subset_inter_left _ (Set.Icc_subset_Icc (by simp [hK]) (by simp [hK]))
  have hP' : μ (I ∩ Set.Ioi 0) ≠ 0 := by
    refine fun h => hn2 (measure_mono_null ?_ h)
    exact Set.inter_subset_inter_left _ (Set.Icc_subset_Icc (by simp [hK]) (by simp [hK]))
  set cE := μ I with hcE
  have hcE0 : cE ≠ 0 := fun h => hN' (measure_mono_null Set.inter_subset_left h)
  have hcEt : cE ≠ ⊤ := measure_ne_top _ _
  set c := cE.toReal with hc
  have hc0 : 0 < c := ENNReal.toReal_pos hcE0 hcEt
  have hc1 : c ≤ 1 := by
    rw [hc]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hcof : ENNReal.ofReal c = cE := ENNReal.ofReal_toReal hcEt
  set F1 : Measure ℝ := cE⁻¹ • μ.restrict I with hF1
  set F2 : Measure ℝ := (ENNReal.ofReal (1 - c/2))⁻¹ •
    (ENNReal.ofReal (1/2) • μ.restrict I + μ.restrict Iᶜ) with hF2
  have hq0 : ENNReal.ofReal (1 - c/2) ≠ 0 := by simp; linarith
  have hF1p : IsProbabilityMeasure F1 := ⟨by
    simp only [hF1, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hcE0 hcEt⟩
  have hF2p : IsProbabilityMeasure F2 := ⟨by
    simp only [hF2, Measure.smul_apply, Measure.add_apply, Measure.restrict_apply_univ, smul_eq_mul]
    rw [prob_compl_eq_one_sub hIm, ← hcE, ← hcof, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub _ hc0.le, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by linarith), ENNReal.ofReal_one]
    have : 1 / 2 * c + (1 - c) = 1 - c / 2 := by ring
    rw [this, ENNReal.inv_mul_cancel hq0 ENNReal.ofReal_ne_top]⟩
  have hdec : μ = ENNReal.ofReal (c/2) • F1 + ENNReal.ofReal (1 - c/2) • F2 := by
    rw [hF1, hF2, smul_smul, smul_smul, ENNReal.mul_inv_cancel hq0 ENNReal.ofReal_ne_top, one_smul]
    have : ENNReal.ofReal (c/2) * cE⁻¹ = ENNReal.ofReal (1/2) := by
      rw [← hcof, ← ENNReal.ofReal_inv_of_pos hc0, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; field_simp
    rw [this, ← add_assoc, ← add_smul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
    exact (Measure.restrict_add_restrict_compl hIm).symm
  have hp0 : 0 < c/2 := by positivity
  have hp1 : c/2 < 1 := by linarith
  -- integrability transfers
  have htr : ∀ f : ℝ → ℝ, Integrable f μ → Integrable f F1 ∧ Integrable f F2 := by
    intro f hf
    rw [hdec] at hf
    exact (S194K_int_iff hp0 hp1).1 hf
  have hmeas : AEMeasurable (fun x : ℝ => x) F1 := measurable_id.aemeasurable
  have hF1x2 : MemLp (fun x : ℝ => x) 2 F1 :=
    (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 (htr _ hx2).1
  set m1 := ∫ x, x ∂F1 with hm1
  set v1 := variance (fun x : ℝ => x) F1 with hv1
  have hv1nn : 0 ≤ v1 := variance_nonneg _ _
  have hv1pos : 0 < v1 := by
    rcases hv1nn.lt_or_eq with h | h
    · exact h
    exfalso
    have hae := ae_eq_integral_of_variance_eq_zero hF1x2 h.symm
    rw [ae_iff] at hae
    have key : ∀ T : Set ℝ, MeasurableSet T → μ (I ∩ T) ≠ 0 → (∀ x ∈ T, x ≠ m1) → False := by
      intro T hT hμT hx
      have : F1 T = 0 := measure_mono_null (fun x hxT => hx x hxT) hae
      rw [hF1, Measure.smul_apply, Measure.restrict_apply hT, smul_eq_mul, mul_eq_zero,
        ENNReal.inv_eq_zero, Set.inter_comm] at this
      rcases this with h | h
      · exact hcEt h
      · exact hμT h
    rcases le_or_gt 0 m1 with hm | hm
    · exact key _ measurableSet_Iio hN' (fun x hx => by simp at hx; intro h; linarith)
    · exact key _ measurableSet_Ioi hP' (fun x hx => by simp at hx; intro h; linarith)
  set G := gaussianReal m1 v1.toNNReal with hG
  have hGx1 : Integrable (fun x : ℝ => x) G := (memLp_id_gaussianReal' 1 (by simp)).integrable le_rfl
  have hGx2 : Integrable (fun x : ℝ => x ^ 2) G := (memLp_id_gaussianReal' 2 (by simp)).integrable_sq
  have hGm : ∫ x, x ∂G = m1 := integral_id_gaussianReal
  have hGv : variance (fun x : ℝ => x) G = v1 := by
    have := variance_id_gaussianReal (μ := m1) (v := v1.toNNReal)
    rw [Real.coe_toNNReal _ hv1nn] at this
    exact this
  have hG2 : ∫ x, x ^ 2 ∂G = v1 + m1 ^ 2 := by
    have := variance_eq_sub (μ := G) (X := fun x : ℝ => x) (memLp_id_gaussianReal' 2 (by simp))
    rw [hGv, hGm] at this
    simp only [Pi.pow_apply] at this
    linarith
  have hF12 : ∫ x, x ^ 2 ∂F1 = v1 + m1 ^ 2 := by
    have := variance_eq_sub hF1x2
    rw [← hv1, ← hm1] at this
    simp only [Pi.pow_apply] at this
    linarith
  have hμ1 := S194K_int_eq hp0 hp1 (htr _ hx1).1 (htr _ hx1).2
  have hμ2 := S194K_int_eq hp0 hp1 (htr _ hx2).1 (htr _ hx2).2
  rw [← hdec] at hμ1 hμ2
  have hν1 : ∫ x, x ∂(ENNReal.ofReal (c/2) • G + ENNReal.ofReal (1 - c/2) • F2) = 0 := by
    rw [S194K_int_eq hp0 hp1 hGx1 (htr _ hx1).2, hGm, ← hmean, hμ1]
  refine ⟨c/2, F1, F2, hF1p, hF2p, hp0, hp1, ⟨K, ?_⟩, hv1pos, hdec, ⟨a₀, ha₀, ?_⟩, hν1, ?_⟩
  · simp [hF1, Measure.smul_apply, ← hI, ENNReal.inv_mul_cancel hcE0 hcEt, ← hcE]
  · intro a ha
    exact (S194K_int_iff hp0 hp1).2 ⟨integrable_exp_mul_gaussianReal a, (htr _ (hexp a ha)).2⟩
  · rw [variance_of_integral_eq_zero (X := fun x : ℝ => x) aemeasurable_id hν1,
      S194K_int_eq hp0 hp1 hGx2 (htr _ hx2).2, hG2, ← hF12, ← hμ2,
      ← variance_of_integral_eq_zero (X := fun x : ℝ => x) aemeasurable_id hmean, hvariance]
