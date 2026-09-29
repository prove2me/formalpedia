-- Prove2me | solution 1 for DouglasVacua.continuum_flux_shell_density
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T20:52:27.160979+00:00
-- url     : https://prove2.me/submissions/395c11c4-c4e3-4fde-b728-fda0ab8e4109

import Mathlib

open Real MeasureTheory

lemma dvSqrtPow (x : ℝ) (hx : 0 ≤ x) (J : ℕ) : Real.sqrt x ^ J = x ^ ((J : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

lemma dvFluxVolume (J : ℕ) (c V : ℝ) (hc : 0 < c) (hV : 0 ≤ V) :
    volume {x : Fin J → ℝ | c * ∑ i, x i ^ 2 ≤ V} =
      ENNReal.ofReal (π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2 + 1) *
        (V / c) ^ ((J : ℝ) / 2)) := by
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · subst hJ
    have hU : {x : Fin 0 → ℝ | c * ∑ i, x i ^ 2 ≤ V} = Set.univ := by
      ext x
      simp [hV]
    rw [hU, volume_pi, Measure.pi_univ]
    simp
  · have : Nonempty (Fin J) := ⟨⟨0, hJ⟩⟩
    have hVc : 0 ≤ V / c := div_nonneg hV hc.le
    set r := Real.sqrt (V / c) with hr
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hS : {x : Fin J → ℝ | c * ∑ i, x i ^ 2 ≤ V} =
        (WithLp.toLp 2) ⁻¹' (Metric.closedBall (0 : EuclideanSpace ℝ (Fin J)) r) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_closedBall_zero_iff]
      rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hr0 two_ne_zero, EuclideanSpace.norm_sq_eq,
        hr, Real.sq_sqrt hVc, le_div_iff₀ hc, mul_comm]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hS, (PiLp.volume_preserving_toLp (Fin J)).measure_preimage
      measurableSet_closedBall.nullMeasurableSet, EuclideanSpace.volume_closedBall,
      Fintype.card_fin, ← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_mul (pow_nonneg hr0 _)]
    congr 1
    rw [hr, dvSqrtPow _ hVc, dvSqrtPow _ Real.pi_pos.le]
    ring

lemma dvShellIntegral (J : ℕ) (hJ : 1 ≤ J) (c V₁ V₂ : ℝ) (hc : 0 < c)
    (hV₁ : 0 ≤ V₁) (hV : V₁ ≤ V₂) :
    (∫ v in V₁..V₂,
        (2 * π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2)) / 2 *
          c ^ (-((J : ℝ) / 2)) * v ^ ((J : ℝ) / 2 - 1)) =
      π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2 + 1) * (V₂ / c) ^ ((J : ℝ) / 2) -
        π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2 + 1) * (V₁ / c) ^ ((J : ℝ) / 2) := by
  have hV₂ : 0 ≤ V₂ := hV₁.trans hV
  have hJ2 : (0 : ℝ) < (J : ℝ) / 2 := by
    have : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
    linarith
  have hG : 0 < Real.Gamma ((J : ℝ) / 2) := Real.Gamma_pos_of_pos hJ2
  have hcJ : 0 < c ^ ((J : ℝ) / 2) := Real.rpow_pos_of_pos hc _
  have hr : -1 < (J : ℝ) / 2 - 1 := by linarith
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr)]
  have e1 : (J : ℝ) / 2 - 1 + 1 = (J : ℝ) / 2 := by ring
  rw [e1, Real.div_rpow hV₂ hc.le, Real.div_rpow hV₁ hc.le, Real.rpow_neg hc.le,
    Real.Gamma_add_one hJ2.ne']
  field_simp

open Real MeasureTheory in
theorem solution (J : ℕ) (hJ : 1 ≤ J) (c V₁ V₂ : ℝ) (hc : 0 < c)
    (hV₁ : 0 ≤ V₁) (hV : V₁ ≤ V₂) :
    volume {x : Fin J → ℝ | V₁ < c * ∑ i, x i ^ 2 ∧ c * ∑ i, x i ^ 2 ≤ V₂} =
      ENNReal.ofReal (∫ v in V₁..V₂,
        (2 * π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2)) / 2 *
          c ^ (-((J : ℝ) / 2)) * v ^ ((J : ℝ) / 2 - 1)) := by
  have hV₂ : 0 ≤ V₂ := hV₁.trans hV
  have hq : Measurable (fun x : Fin J → ℝ => c * ∑ i, x i ^ 2) := by fun_prop
  have hset : {x : Fin J → ℝ | V₁ < c * ∑ i, x i ^ 2 ∧ c * ∑ i, x i ^ 2 ≤ V₂} =
      {x : Fin J → ℝ | c * ∑ i, x i ^ 2 ≤ V₂} \ {x : Fin J → ℝ | c * ∑ i, x i ^ 2 ≤ V₁} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_le]
    exact and_comm
  have hsub : {x : Fin J → ℝ | c * ∑ i, x i ^ 2 ≤ V₁} ⊆
      {x : Fin J → ℝ | c * ∑ i, x i ^ 2 ≤ V₂} := fun x hx => le_trans hx hV
  have hA₁ : 0 ≤ π ^ ((J : ℝ) / 2) / Real.Gamma ((J : ℝ) / 2 + 1) * (V₁ / c) ^ ((J : ℝ) / 2) :=
    mul_nonneg (div_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.Gamma_pos_of_pos (by positivity)).le) (Real.rpow_nonneg (div_nonneg hV₁ hc.le) _)
  rw [hset, measure_sdiff hsub (measurableSet_le hq measurable_const).nullMeasurableSet
      (by rw [dvFluxVolume J c V₁ hc hV₁]; exact ENNReal.ofReal_ne_top),
    dvFluxVolume J c V₂ hc hV₂, dvFluxVolume J c V₁ hc hV₁, ← ENNReal.ofReal_sub _ hA₁,
    dvShellIntegral J hJ c V₁ V₂ hc hV₁ hV]

