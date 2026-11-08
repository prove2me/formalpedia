-- Prove2me | solution 1 for CtrlVolMFG.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:39:51.940169+00:00
-- url     : https://prove2.me/submissions/2326cfb8-4588-4100-a325-b607ebea8b33

import Mathlib
import Definitions.Def_CtrlVolMFG_IsSol_3_6

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open CtrlVolMFG in
theorem solution {n : ℕ} (U : Rn n → P2 n → ℝ) (C : ℝ) (hU : IsDisplMono C U) (N : ℕ)
    (x x' : Fin N → Rn n) :
    C * ∑ i, ‖x i - x' i‖ ^ 2 ≤
      ∑ i, inner ℝ (Dx U (x i) (empP2 x) - Dx U (x' i) (empP2 x')) (x i - x' i) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNe : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N : ℝ≥0∞)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hNe
  set π : Measure (Rn n × Rn n) := ((N : ℝ≥0∞)⁻¹) • ∑ i, Measure.dirac (x i, x' i) with hπ
  have hfst : π.map Prod.fst = empMeasure x := by
    rw [hπ, Measure.map_smul, Measure.map_finset_sum' measurable_fst.aemeasurable]
    simp only [Measure.map_dirac' measurable_fst, empMeasure]
  have hsnd : π.map Prod.snd = empMeasure x' := by
    rw [hπ, Measure.map_smul, Measure.map_finset_sum' measurable_snd.aemeasurable]
    simp only [Measure.map_dirac' measurable_snd, empMeasure]
  have hint : ∀ g : Rn n × Rn n → ℝ, Integrable g π := by
    intro g
    apply Integrable.smul_measure _ hNt
    rw [integrable_finsetSum_measure]
    intro i _
    exact integrable_dirac enorm_lt_top
  have hintegral : ∀ g : Rn n × Rn n → ℝ, ∫ w, g w ∂π = (N : ℝ)⁻¹ * ∑ i, g (x i, x' i) := by
    intro g
    rw [hπ, integral_smul_measure,
      integral_finsetSum_measure (fun i _ => integrable_dirac enorm_lt_top)]
    simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  have hL2 : IsL2Pair π := by
    refine ⟨⟨?_⟩, ?_⟩
    · rw [hπ, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
      simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hNe (ENNReal.natCast_ne_top N)
    · rw [hπ, lintegral_smul_measure, lintegral_finsetSum_measure]
      simp only [lintegral_dirac]
      apply ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hNt)
      apply ENNReal.sum_lt_top.mpr
      intro i _
      exact ENNReal.add_lt_top.mpr ⟨ENNReal.pow_lt_top enorm_lt_top,
        ENNReal.pow_lt_top enorm_lt_top⟩
  have h := hU π hL2 (hint _)
  rw [hfst, hsnd, hintegral, hintegral] at h
  simp only at h
  unfold empP2
  have h' : (N : ℝ)⁻¹ * (C * ∑ i, ‖x i - x' i‖ ^ 2) ≤ (N : ℝ)⁻¹ *
      ∑ i, inner ℝ (Dx U (x i) (toP2 (empMeasure x)) - Dx U (x' i) (toP2 (empMeasure x')))
        (x i - x' i) := by
    linarith
  exact le_of_mul_le_mul_left h' (by positivity)
