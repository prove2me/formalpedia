-- Prove2me | solution 1 for ClusterSim.EdgeCut.eqs_35_36
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T23:10:16.68699+00:00
-- url     : https://prove2.me/submissions/df5c7be5-9c9e-4c46-9d60-d8640d66095b

import Definitions.Def_ClusterSim_EdgeCut_Estimator
import Theorems.Thm_ClusterSim_EdgeCut_eq_33

open ClusterSim.EdgeCut MeasureTheory ENNReal

private lemma pow_eight_div_two (K : ℕ) :
    (8 : ℝ) ^ K * (1 / 2 ^ K) * 1 = (2 : ℝ) ^ (2 * K) := by
  have h8 : (8 : ℝ) ^ K = (2 : ℝ) ^ (2 * K) * (2 : ℝ) ^ K := by
    rw [pow_mul, ← mul_pow]
    norm_num
  rw [h8]
  field_simp

theorem solution {G : TensorNetwork} {r : ℕ} (P : Clustering G r)
    (run : (P.Ecut → Fin 8) → Measure ℝ) [∀ s, IsProbabilityMeasure (run s)]
    (hrange : ∀ s, ∀ᵐ t ∂(run s), t ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ s, ((∫ t, t ∂(run s) : ℝ) : ℂ) = value (cut G P.Ecut s)) :
    IsProbabilityMeasure (sampleLaw P run) ∧
      (∀ᵐ x ∂(sampleLaw P run), |x| ≤ (2 : ℝ) ^ (2 * P.Ecut.card)) ∧
      ((∫ x, x ∂(sampleLaw P run) : ℝ) : ℂ) = value G := by
  obtain ⟨heq33, hcoef⟩ := eq_33 G P.Ecut
  have h8_ne_zero : (8 : ℝ≥0∞) ^ P.Ecut.card ≠ 0 := pow_ne_zero _ (by norm_num)
  have h8_ne_top : (8 : ℝ≥0∞) ^ P.Ecut.card ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have h8_inv_ne_top : ((8 : ℝ≥0∞) ^ P.Ecut.card)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr h8_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_⟩
    unfold sampleLaw
    rw [Measure.finset_sum_apply]
    have hterm : ∀ s : P.Ecut → Fin 8,
        ((((8 : ℝ≥0∞) ^ P.Ecut.card)⁻¹ •
          (run s).map (fun t => (8 : ℝ) ^ P.Ecut.card * coefS s * t)) Set.univ) =
        ((8 : ℝ≥0∞) ^ P.Ecut.card)⁻¹ := by
      intro s
      rw [Measure.smul_apply, smul_eq_mul,
        Measure.map_apply (by fun_prop) MeasurableSet.univ,
        Set.preimage_univ, measure_univ, mul_one]
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_coe, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact ENNReal.mul_inv_cancel h8_ne_zero h8_ne_top
  · rw [ae_iff, sampleLaw, Measure.finset_sum_apply, Finset.sum_eq_zero_iff]
    intro s _
    rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero]
    right
    rw [← ae_iff]
    have hmeas_set : MeasurableSet {x : ℝ | |x| ≤ (2 : ℝ) ^ (2 * P.Ecut.card)} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    rw [ae_map_iff (by fun_prop) hmeas_set]
    filter_upwards [hrange s] with t ht
    have ht_abs : |t| ≤ 1 := abs_le.mpr ht
    have hc_abs : |coefS s| = 1 / 2 ^ P.Ecut.card := hcoef s
    change |(8 : ℝ) ^ P.Ecut.card * coefS s * t| ≤ (2 : ℝ) ^ (2 * P.Ecut.card)
    rw [abs_mul, abs_mul, abs_of_pos (by positivity), hc_abs, ← pow_eight_div_two P.Ecut.card]
    exact mul_le_mul_of_nonneg_left ht_abs (by positivity)
  · unfold sampleLaw
    have hint : ∀ s ∈ (Finset.univ : Finset (P.Ecut → Fin 8)),
        Integrable (fun x : ℝ => x)
          (((8 : ℝ≥0∞) ^ P.Ecut.card)⁻¹ •
            (run s).map (fun t => (8 : ℝ) ^ P.Ecut.card * coefS s * t)) := by
      intro s _
      have hi0 : Integrable (fun t : ℝ => t) (run s) :=
        Integrable.of_mem_Icc (-1) 1 aemeasurable_id (hrange s)
      have hi1 : Integrable (fun t : ℝ => ((8 : ℝ) ^ P.Ecut.card * coefS s) * t) (run s) :=
        hi0.const_mul _
      have hi2 : Integrable (fun x : ℝ => x)
          ((run s).map (fun t => (8 : ℝ) ^ P.Ecut.card * coefS s * t)) :=
        (integrable_map_measure aestronglyMeasurable_id (by fun_prop)).mpr hi1
      exact hi2.smul_measure h8_inv_ne_top
    rw [integral_finsetSum_measure hint]
    have hterm_int : ∀ s : P.Ecut → Fin 8,
        (∫ x, x ∂(((8 : ℝ≥0∞) ^ P.Ecut.card)⁻¹ •
          (run s).map (fun t => (8 : ℝ) ^ P.Ecut.card * coefS s * t))) =
        ((8 : ℝ) ^ P.Ecut.card)⁻¹ * (((8 : ℝ) ^ P.Ecut.card * coefS s) * ∫ t, t ∂(run s)) := by
      intro s
      have hmap : (∫ x, x ∂(run s).map (fun t => (8 : ℝ) ^ P.Ecut.card * coefS s * t)) =
          ∫ t, ((8 : ℝ) ^ P.Ecut.card * coefS s) * t ∂(run s) :=
        integral_map (by fun_prop) aestronglyMeasurable_id
      rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_pow,
        ENNReal.toReal_ofNat, hmap, integral_const_mul]
    simp_rw [hterm_int]
    push_cast
    rw [heq33]
    apply Finset.sum_congr rfl
    intro s _
    rw [hmean s, mul_assoc ((8 : ℂ) ^ P.Ecut.card)]
