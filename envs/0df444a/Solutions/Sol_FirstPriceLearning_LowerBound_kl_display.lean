-- Prove2me | solution 1 for FirstPriceLearning.LowerBound.kl_display
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:32:52.517618+00:00
-- url     : https://prove2.me/submissions/bd5ea058-eb33-4b2c-9ac8-4b9fee31afa0

import Mathlib
import Definitions.Def_FirstPriceLearning_LowerBound_TwoPointLaws

set_option autoImplicit false
open MeasureTheory InformationTheory ProbabilityTheory FirstPriceLearning.LowerBound

lemma twoPoint_prob (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsProbabilityMeasure (twoPointLaw p) := by
  constructor
  unfold twoPointLaw
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
    Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, Measure.dirac_apply_of_mem,
    Set.mem_univ, ENNReal.smul_def]
  rw [show ((p.toNNReal : ENNReal)) = ENNReal.ofReal p from rfl,
    show (((1 - p).toNNReal : ENNReal)) = ENNReal.ofReal (1 - p) from rfl, ← ENNReal.ofReal_add h0 (by linarith)]
  simp

lemma klDiv_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  apply le_antisymm (klDiv_map_le μ ν e.measurable)
  have := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  rw [Measure.map_map e.symm.measurable e.measurable, Measure.map_map e.symm.measurable e.measurable] at this
  simpa using this

lemma klDiv_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (P1 P2 : Measure α)
    (Q1 Q2 : Measure β) [IsProbabilityMeasure P1] [IsProbabilityMeasure P2]
    [IsProbabilityMeasure Q1] [IsProbabilityMeasure Q2] :
    klDiv (P1.prod Q1) (P2.prod Q2) = klDiv P1 P2 + klDiv Q1 Q2 := by
  have h1 : P1.prod Q1 = P1.compProd (Kernel.const α Q1) := (Measure.compProd_const).symm
  have h2 : P2.prod Q2 = P2.compProd (Kernel.const α Q2) := (Measure.compProd_const).symm
  have h3 : P1.prod Q2 = P1.compProd (Kernel.const α Q2) := (Measure.compProd_const).symm
  rw [h1, h2, klDiv_compProd_eq_add, ← h1, ← h3]
  congr 1
  rw [← klDiv_map_equiv (MeasurableEquiv.prodComm) (P1.prod Q1) (P1.prod Q2)]
  have e1 : (P1.prod Q1).map (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α) = Q1.prod P1 := by
    exact Measure.prod_swap
  have e2 : (P1.prod Q2).map (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α) = Q2.prod P1 := by
    exact Measure.prod_swap
  rw [e1, e2, ← Measure.compProd_const, ← Measure.compProd_const, klDiv_compProd_left]

lemma klDiv_pi (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (T : ℕ) :
    klDiv (Measure.pi fun _ : Fin T => P) (Measure.pi fun _ : Fin T => Q) = T * klDiv P Q := by
  induction T with
  | zero =>
    have : (Measure.pi fun _ : Fin 0 => P) = Measure.pi fun _ : Fin 0 => Q := by
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
    rw [this, klDiv_self]; simp
  | succ n ih =>
    have hP := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).map_eq
    have hQ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => Q) 0).map_eq
    rw [← klDiv_map_equiv (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0), hP, hQ,
      klDiv_prod, ih]
    push_cast
    ring

noncomputable def dens2 (p q : ℝ) : ℝ → ENNReal := fun x =>
  if x = 1 / 3 then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q))

lemma dens2_meas (p q : ℝ) : Measurable (dens2 p q) := by
  unfold dens2
  exact Measurable.ite (measurableSet_singleton _) measurable_const measurable_const

lemma twoPoint_density (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    twoPointLaw p = (twoPointLaw q).withDensity (dens2 p q) := by
  ext s hs
  rw [withDensity_apply _ hs, ← lintegral_indicator hs]
  have hm : Measurable (s.indicator (dens2 p q)) := (dens2_meas p q).indicator hs
  have e1 : ∫⁻ x, s.indicator (dens2 p q) x ∂(twoPointLaw q) =
      (q.toNNReal : ENNReal) * s.indicator (dens2 p q) (1 / 3) +
        ((1 - q).toNNReal : ENNReal) * s.indicator (dens2 p q) (2 / 3) := by
    unfold twoPointLaw
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac' _ hm, lintegral_dirac' _ hm]
    simp [ENNReal.smul_def]
  rw [e1]
  unfold twoPointLaw
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply' _ hs, ENNReal.smul_def,
    smul_eq_mul]
  have g1 : dens2 p q (1 / 3) = ENNReal.ofReal (p / q) := by simp [dens2]
  have g2 : dens2 p q (2 / 3) = ENNReal.ofReal ((1 - p) / (1 - q)) := by
    simp only [dens2]; rw [if_neg]; norm_num
  have k1 : (q.toNNReal : ENNReal) * ENNReal.ofReal (p / q) = (p.toNNReal : ENNReal) := by
    rw [show ((q.toNNReal : ENNReal)) = ENNReal.ofReal q from rfl,
      ← ENNReal.ofReal_mul hq0.le]
    rw [show (p.toNNReal : ENNReal) = ENNReal.ofReal p from rfl]
    congr 1; field_simp
  have k2 : ((1 - q).toNNReal : ENNReal) * ENNReal.ofReal ((1 - p) / (1 - q)) =
      ((1 - p).toNNReal : ENNReal) := by
    rw [show (((1 - q).toNNReal : ENNReal)) = ENNReal.ofReal (1 - q) from rfl,
      ← ENNReal.ofReal_mul (by linarith)]
    rw [show ((1 - p).toNNReal : ENNReal) = ENNReal.ofReal (1 - p) from rfl]
    have : (1 - q) ≠ 0 := (by linarith : (0:ℝ) < 1 - q).ne'
    congr 1; field_simp
  classical
  by_cases h1 : (1 / 3 : ℝ) ∈ s <;> by_cases h2 : (2 / 3 : ℝ) ∈ s <;>
    simp only [Set.indicator_apply, Pi.one_apply, h1, h2, if_true, if_false, g1, g2, k1, k2,
      mul_one, mul_zero, add_zero, zero_add]

lemma kl_two (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    klDiv (twoPointLaw p) (twoPointLaw q) =
      ENNReal.ofReal (p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) := by
  haveI := twoPoint_prob p hp0.le hp1.le
  haveI := twoPoint_prob q hq0.le hq1.le
  have hd := twoPoint_density p q hp0 hp1 hq0 hq1
  have hac : twoPointLaw p ≪ twoPointLaw q := by
    rw [hd]; exact withDensity_absolutelyContinuous _ _
  have hrn : ∀ᵐ x ∂(twoPointLaw p), (twoPointLaw p).rnDeriv (twoPointLaw q) x = dens2 p q x := by
    have := Measure.rnDeriv_withDensity (twoPointLaw q) (dens2_meas p q)
    rw [← hd] at this
    exact hac.ae_le this
  set h : ℝ → ℝ := fun x => Real.log (dens2 p q x).toReal with hh
  have hbound : ∀ x, ‖h x‖ ≤ |Real.log (p / q)| + |Real.log ((1 - p) / (1 - q))| := by
    intro x
    simp only [hh, dens2]
    split_ifs
    · rw [ENNReal.toReal_ofReal (by positivity), Real.norm_eq_abs]; linarith [abs_nonneg (Real.log ((1 - p) / (1 - q)))]
    · rw [ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith)), Real.norm_eq_abs]
      linarith [abs_nonneg (Real.log (p / q))]
  have hhm : Measurable h := by
    show Measurable (fun x => Real.log (dens2 p q x).toReal)
    exact (Measurable.log (ENNReal.measurable_toReal.comp (dens2_meas p q)))
  have hint : Integrable h (twoPointLaw p) :=
    Integrable.of_bound hhm.aestronglyMeasurable _ (ae_of_all _ hbound)
  have hllr : llr (twoPointLaw p) (twoPointLaw q) =ᵐ[twoPointLaw p] h := by
    filter_upwards [hrn] with x hx
    simp [llr, hx, hh]
  have hint2 : Integrable (llr (twoPointLaw p) (twoPointLaw q)) (twoPointLaw p) :=
    hint.congr hllr.symm
  rw [klDiv_of_ac_of_integrable hac hint2, integral_congr_ae hllr]
  have hI : ∫ x, h x ∂(twoPointLaw p) = p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) := by
    unfold twoPointLaw
    have i1 : Integrable h (p.toNNReal • Measure.dirac (1 / 3 : ℝ)) :=
      Integrable.of_bound hhm.aestronglyMeasurable _ (ae_of_all _ hbound)
    have i2 : Integrable h ((1 - p).toNNReal • Measure.dirac (2 / 3 : ℝ)) :=
      Integrable.of_bound hhm.aestronglyMeasurable _ (ae_of_all _ hbound)
    rw [integral_add_measure i1 i2, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      integral_dirac, integral_dirac]
    have g1 : h (1 / 3) = Real.log (p / q) := by simp [hh, dens2, ENNReal.toReal_ofReal (div_nonneg hp0.le hq0.le)]
    have g2 : h (2 / 3) = Real.log ((1 - p) / (1 - q)) := by
      simp only [hh, dens2]; rw [if_neg (by norm_num), ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]
    rw [g1, g2]
    simp [NNReal.smul_def, Real.coe_toNNReal _ hp0.le, Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ 1 - p)]
  rw [hI]
  simp

lemma Fx_bound (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    (1 / 2 - Δ) * Real.log ((1 / 2 - Δ) / (1 / 2 + Δ)) +
      (1 / 2 + Δ) * Real.log ((1 / 2 + Δ) / (1 / 2 - Δ)) ≤ 32 * Δ ^ 2 := by
  have hb : 0 < 1 / 2 - Δ := by linarith
  have ha : 0 < 1 / 2 + Δ := by linarith
  have h1 : Real.log ((1 / 2 - Δ) / (1 / 2 + Δ)) = - Real.log ((1 / 2 + Δ) / (1 / 2 - Δ)) := by
    rw [← Real.log_inv, inv_div]
  have h2 : Real.log ((1 / 2 + Δ) / (1 / 2 - Δ)) ≤ (1 / 2 + Δ) / (1 / 2 - Δ) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos ha hb)
  have h3 : (1 / 2 + Δ) / (1 / 2 - Δ) - 1 ≤ 8 * Δ := by
    rw [div_sub_one hb.ne', div_le_iff₀ hb]; nlinarith
  rw [h1]
  nlinarith [sq_nonneg Δ]

lemma kl_pair (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    klDiv (lawG1 Δ) (lawG2 Δ) = ENNReal.ofReal ((1 / 2 - Δ) * Real.log ((1 / 2 - Δ) / (1 / 2 + Δ))
          + (1 / 2 + Δ) * Real.log ((1 / 2 + Δ) / (1 / 2 - Δ))) ∧
    klDiv (lawG2 Δ) (lawG1 Δ) = ENNReal.ofReal ((1 / 2 - Δ) * Real.log ((1 / 2 - Δ) / (1 / 2 + Δ))
          + (1 / 2 + Δ) * Real.log ((1 / 2 + Δ) / (1 / 2 - Δ))) := by
  constructor
  · unfold lawG1 lawG2
    rw [kl_two _ _ (by linarith) (by linarith) (by linarith) (by linarith)]
    congr 1
    rw [show 1 - (1 / 2 + Δ) = 1 / 2 - Δ by ring, show 1 - (1 / 2 - Δ) = 1 / 2 + Δ by ring]
    ring
  · unfold lawG1 lawG2
    rw [kl_two _ _ (by linarith) (by linarith) (by linarith) (by linarith)]
    congr 1
    rw [show 1 - (1 / 2 + Δ) = 1 / 2 - Δ by ring, show 1 - (1 / 2 - Δ) = 1 / 2 + Δ by ring]

theorem solution (T : ℕ) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    klDiv (Measure.pi fun _ : Fin T => lawG1 Δ) (Measure.pi fun _ : Fin T => lawG2 Δ) =
        (T : ENNReal) * klDiv (lawG1 Δ) (lawG2 Δ) ∧
    klDiv (lawG1 Δ) (lawG2 Δ) =
        ENNReal.ofReal ((1 / 2 - Δ) * Real.log ((1 / 2 - Δ) / (1 / 2 + Δ))
          + (1 / 2 + Δ) * Real.log ((1 / 2 + Δ) / (1 / 2 - Δ))) ∧
    klDiv (Measure.pi fun _ : Fin T => lawG1 Δ) (Measure.pi fun _ : Fin T => lawG2 Δ) ≤
        ENNReal.ofReal (32 * T * Δ ^ 2) ∧
    klDiv (Measure.pi fun _ : Fin T => lawG2 Δ) (Measure.pi fun _ : Fin T => lawG1 Δ) ≤
        ENNReal.ofReal (32 * T * Δ ^ 2) := by
  haveI : IsProbabilityMeasure (lawG1 Δ) := twoPoint_prob _ (by linarith) (by linarith)
  haveI : IsProbabilityMeasure (lawG2 Δ) := twoPoint_prob _ (by linarith) (by linarith)
  obtain ⟨k12, k21⟩ := kl_pair Δ hΔ0 hΔ1
  have hF := Fx_bound Δ hΔ0 hΔ1
  have hT : ∀ F : ℝ, F ≤ 32 * Δ ^ 2 → (T : ENNReal) * ENNReal.ofReal F ≤ ENNReal.ofReal (32 * T * Δ ^ 2) := by
    intro F hFF
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg T)]
    apply ENNReal.ofReal_le_ofReal
    have : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    nlinarith
  refine ⟨klDiv_pi _ _ T, k12, ?_, ?_⟩
  · rw [klDiv_pi, k12]; exact hT _ hF
  · rw [klDiv_pi, k21]; exact hT _ hF
