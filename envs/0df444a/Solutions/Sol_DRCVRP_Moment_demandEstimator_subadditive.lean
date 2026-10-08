-- Prove2me | solution 1 for DRCVRP.Moment.demandEstimator_subadditive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T14:57:38.856842+00:00
-- url     : https://prove2.me/submissions/97bd6653-b2f4-4ab2-8e1d-cf760c526e40

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Moment_AmbiguitySet

open MeasureTheory
open MeasureTheory Filter Topology

namespace DRCVRP.Moment

lemma de_cond_point {n p : ℕ} (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (hint : Integrable (fun x : Fin n → ℝ => x) P)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (hφ : ∀ l, ConvexOn ℝ Set.univ (φ l))
    (hφi : ∀ l, Integrable (φ l) P)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C) (hCc : IsClosed C) (d : Fin n → ℝ)
    (B : Set (Fin n → ℝ)) (hd : P B = 0 → d ∈ C)
    (hBC : ∀ᵐ x ∂P.restrict B, x ∈ C) :
    ∃ q ∈ C, P.real B • q = ∫ x in B, x ∂P ∧ ∀ l, P.real B * φ l q ≤ ∫ x in B, φ l x ∂P := by
  by_cases h : P B = 0
  · refine ⟨d, hd h, ?_, ?_⟩
    · have : P.restrict B = 0 := Measure.restrict_eq_zero.mpr h
      rw [this, integral_zero_measure, measureReal_def, h]; simp
    · intro l
      have : P.restrict B = 0 := Measure.restrict_eq_zero.mpr h
      rw [this, integral_zero_measure, measureReal_def, h]; simp
  · have hpos : 0 < P.real B := ENNReal.toReal_pos h (measure_ne_top _ _)
    refine ⟨⨍ x in B, x ∂P, hC.set_average_mem hCc h (measure_ne_top _ _) hBC hint.integrableOn,
      ?_, ?_⟩
    · rw [setAverage_eq, smul_inv_smul₀ hpos.ne']
    · intro l
      have hj := (hφ l).map_set_average_le ((hφ l).continuousOn isOpen_univ) isClosed_univ h
        (measure_ne_top _ _) (Filter.Eventually.of_forall (fun x => Set.mem_univ x))
        hint.integrableOn (hφi l).integrableOn
      conv_rhs at hj => rw [setAverage_eq, smul_eq_mul]
      have := mul_le_mul_of_nonneg_left hj hpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this

lemma de_twoPoint_integral {n : ℕ} (p₁ p₂ : ℝ) (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂) (q₁ q₂ : Fin n → ℝ)
    (g : (Fin n → ℝ) → ℝ) :
    Integrable g (twoPointMeasure p₁ p₂ q₁ q₂) ∧
      ∫ x, g x ∂(twoPointMeasure p₁ p₂ q₁ q₂) = p₁ * g q₁ + p₂ * g q₂ := by
  have i1 : Integrable g (Measure.dirac q₁) := integrable_dirac (by simp)
  have i2 : Integrable g (Measure.dirac q₂) := integrable_dirac (by simp)
  have j1 : Integrable g (ENNReal.ofReal p₁ • Measure.dirac q₁) := i1.smul_measure (by simp)
  have j2 : Integrable g (ENNReal.ofReal p₂ • Measure.dirac q₂) := i2.smul_measure (by simp)
  refine ⟨j1.add_measure j2, ?_⟩
  unfold twoPointMeasure
  rw [integral_add_measure j1 j2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]
  simp [smul_eq_mul]

lemma de_twoPoint_apply {n : ℕ} (p₁ p₂ : ℝ) (q₁ q₂ : Fin n → ℝ) (s : Set (Fin n → ℝ)) :
    twoPointMeasure p₁ p₂ q₁ q₂ s =
      ENNReal.ofReal p₁ * s.indicator 1 q₁ + ENNReal.ofReal p₂ * s.indicator 1 q₂ := by
  unfold twoPointMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply,
    Measure.dirac_apply]
  simp

lemma de_twoPoint_mem {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (σ : Fin p → ℝ) (p₁ p₂ : ℝ) (q₁ q₂ : Fin n → ℝ)
    (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂) (h12 : p₁ + p₂ = 1)
    (hq1 : q₁ ∈ Set.Icc qlo qhi) (hq2 : q₂ ∈ Set.Icc qlo qhi)
    (hm : ∀ i, p₁ * q₁ i + p₂ * q₂ i = μ i)
    (hs : ∀ l, p₁ * φ l q₁ + p₂ * φ l q₂ ≤ σ l) :
    twoPointMeasure p₁ p₂ q₁ q₂ ∈ momentAmbiguitySet qlo qhi μ φ σ := by
  have hone : ENNReal.ofReal p₁ + ENNReal.ofReal p₂ = 1 := by
    rw [← ENNReal.ofReal_add h1 h2, h12, ENNReal.ofReal_one]
  refine ⟨⟨?_⟩, ?_, ?_, ?_⟩
  · rw [de_twoPoint_apply]; simp [hone]
  · rw [de_twoPoint_apply]; simp [hq1, hq2, hone]
  · intro i
    obtain ⟨hi, he⟩ := de_twoPoint_integral p₁ p₂ h1 h2 q₁ q₂ (fun q => q i)
    exact ⟨hi, by rw [he]; exact hm i⟩
  · intro l
    obtain ⟨hi, he⟩ := de_twoPoint_integral p₁ p₂ h1 h2 q₁ q₂ (φ l)
    exact ⟨hi, by rw [he]; exact hs l⟩

lemma de_bdd {n : ℕ} (qlo qhi : Fin n → ℝ) (P : Measure (Fin n → ℝ))
    (hbox : P (Set.Icc qlo qhi) = 1) [IsProbabilityMeasure P] (U : Finset (Fin n)) (α : ℝ)
    (hα : 0 < α) :
    BddBelow {y : ℝ | ENNReal.ofReal α ≤ P {ω | (fun q => ∑ i ∈ U, q i) ω ≤ y}} := by
  refine ⟨∑ i ∈ U, qlo i, ?_⟩
  intro y hy
  replace hy : ENNReal.ofReal α ≤ P {ω | (fun q => ∑ i ∈ U, q i) ω ≤ y} := hy
  by_contra hlt
  push_neg at hlt
  have hsub : {ω : Fin n → ℝ | (fun q => ∑ i ∈ U, q i) ω ≤ y} ⊆ (Set.Icc qlo qhi)ᶜ := by
    intro x hx hxI
    simp only [Set.mem_setOf_eq] at hx
    have : ∑ i ∈ U, qlo i ≤ ∑ i ∈ U, x i := Finset.sum_le_sum (fun i _ => hxI.1 i)
    linarith
  have hc : P (Set.Icc qlo qhi)ᶜ = 0 := by
    rw [prob_compl_eq_zero_iff measurableSet_Icc]; exact hbox
  have := measure_mono_null hsub hc
  rw [this] at hy
  have : (0 : ENNReal) < ENNReal.ofReal α := ENNReal.ofReal_pos.mpr hα
  exact absurd hy (not_le.mpr this)

lemma de_var_le {n : ℕ} (qlo qhi : Fin n → ℝ) (P : Measure (Fin n → ℝ))
    (hbox : P (Set.Icc qlo qhi) = 1) [IsProbabilityMeasure P] (U : Finset (Fin n)) (α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ U, q i) α ≤ ∑ i ∈ U, qhi i := by
  unfold MultistageStochastic.valueAtRisk
  refine csInf_le (de_bdd qlo qhi P hbox U α hα) ?_
  simp only [Set.mem_setOf_eq]
  calc ENNReal.ofReal α ≤ 1 := ENNReal.ofReal_le_one.mpr hα1
    _ = P (Set.Icc qlo qhi) := hbox.symm
    _ ≤ _ := measure_mono (fun x hx => Finset.sum_le_sum (fun i _ => hx.2 i))

lemma de_twoPoint_var_ge {n : ℕ} (p₁ p₂ ε : ℝ) (q₁ q₂ : Fin n → ℝ)
    (h1 : 0 ≤ p₁) (h12 : p₁ + p₂ = 1) (hp2 : ε < p₂) (hε0 : 0 < ε) (hε1 : ε < 1)
    (U : Finset (Fin n)) :
    ∑ i ∈ U, q₂ i ≤ MultistageStochastic.valueAtRisk (twoPointMeasure p₁ p₂ q₁ q₂)
      (fun q => ∑ i ∈ U, q i) (1 - ε) := by
  have h2 : 0 ≤ p₂ := by linarith
  have hone : ENNReal.ofReal p₁ + ENNReal.ofReal p₂ = 1 := by
    rw [← ENNReal.ofReal_add h1 h2, h12, ENNReal.ofReal_one]
  unfold MultistageStochastic.valueAtRisk
  refine le_csInf ⟨max (∑ i ∈ U, q₁ i) (∑ i ∈ U, q₂ i), ?_⟩ ?_
  · simp only [Set.mem_setOf_eq]
    rw [de_twoPoint_apply]
    have a1 : q₁ ∈ {ω : Fin n → ℝ | ∑ i ∈ U, ω i ≤ max (∑ i ∈ U, q₁ i) (∑ i ∈ U, q₂ i)} :=
      by show ∑ i ∈ U, q₁ i ≤ _; exact le_max_left _ _
    have a2 : q₂ ∈ {ω : Fin n → ℝ | ∑ i ∈ U, ω i ≤ max (∑ i ∈ U, q₁ i) (∑ i ∈ U, q₂ i)} :=
      by show ∑ i ∈ U, q₂ i ≤ _; exact le_max_right _ _
    rw [Set.indicator_of_mem a1, Set.indicator_of_mem a2]
    simp only [Pi.one_apply, mul_one, hone]
    exact ENNReal.ofReal_le_one.mpr (by linarith)
  · intro y hy
    by_contra hlt
    push_neg at hlt
    simp only [Set.mem_setOf_eq] at hy
    rw [de_twoPoint_apply] at hy
    have a2 : q₂ ∉ {ω : Fin n → ℝ | ∑ i ∈ U, ω i ≤ y} := by
      simp only [Set.mem_setOf_eq, not_le]; exact hlt
    rw [Set.indicator_of_notMem a2] at hy
    have : ENNReal.ofReal p₁ * Set.indicator {ω : Fin n → ℝ | ∑ i ∈ U, ω i ≤ y} 1 q₁ ≤
        ENNReal.ofReal p₁ := by
      by_cases hq : q₁ ∈ {ω : Fin n → ℝ | ∑ i ∈ U, ω i ≤ y}
      · rw [Set.indicator_of_mem hq]; simp
      · rw [Set.indicator_of_notMem hq]; simp
    have h3 : ENNReal.ofReal (1 - ε) ≤ ENNReal.ofReal p₁ := by
      refine le_trans hy ?_; simpa using this
    have := (ENNReal.ofReal_le_ofReal_iff h1).mp h3
    linarith

lemma de_exists_twoPoint {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (σ : Fin p → ℝ) (ε : ℝ)
    (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (hφ : ∀ l, ConvexOn ℝ Set.univ (φ l))
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (P : Measure (Fin n → ℝ)) (hP : P ∈ momentAmbiguitySet qlo qhi μ φ σ)
    (U : Finset (Fin n)) (v : ℝ)
    (hv : v < MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ U, q i) (1 - ε)) :
    ∃ p₁ p₂ : ℝ, ∃ q₁ q₂ : Fin n → ℝ, 0 ≤ p₁ ∧ ε < p₂ ∧ p₁ + p₂ = 1 ∧
      q₁ ∈ Set.Icc qlo qhi ∧ q₂ ∈ Set.Icc qlo qhi ∧ v ≤ ∑ i ∈ U, q₂ i ∧
      twoPointMeasure p₁ p₂ q₁ q₂ ∈ momentAmbiguitySet qlo qhi μ φ σ := by
  obtain ⟨hprob, hbox, hmean, hdisp⟩ := hP
  have hint : Integrable (fun x : Fin n → ℝ => x) P := Integrable.of_eval (fun i => (hmean i).1)
  have hφi : ∀ l, Integrable (φ l) P := fun l => (hdisp l).1
  set f : (Fin n → ℝ) → ℝ := fun q => ∑ i ∈ U, q i with hf
  have hfc : Continuous f := by rw [hf]; fun_prop
  set A : Set (Fin n → ℝ) := {x | v < f x} with hAdef
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hfc.measurable
  have hAc : Aᶜ = {x | f x ≤ v} := by ext x; simp [hAdef]
  -- P {f ≤ v} < 1 - ε
  have hlt : P {x | f x ≤ v} < ENNReal.ofReal (1 - ε) := by
    by_contra hge
    push_neg at hge
    have : MultistageStochastic.valueAtRisk P f (1 - ε) ≤ v := by
      unfold MultistageStochastic.valueAtRisk
      exact csInf_le (de_bdd qlo qhi P hbox U (1 - ε) (by linarith)) hge
    linarith
  have hcr : P.real Aᶜ < 1 - ε := by
    rw [hAc, measureReal_def]; exact ENNReal.toReal_lt_of_lt_ofReal hlt
  have hsum : P.real A + P.real Aᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hAm]; simp
  have hpA : ε < P.real A := by linarith
  have hA0 : P A ≠ 0 := by
    intro h; rw [measureReal_def, h] at hpA; simp at hpA; linarith
  have hboxae : ∀ᵐ x ∂P, x ∈ Set.Icc qlo qhi := by
    rw [ae_iff]
    have : {a : Fin n → ℝ | a ∉ Set.Icc qlo qhi} = (Set.Icc qlo qhi)ᶜ := rfl
    rw [this, prob_compl_eq_zero_iff measurableSet_Icc]; exact hbox
  have hμI : μ ∈ Set.Icc qlo qhi := ⟨fun i => (hμ i).1.le, fun i => (hμ i).2.le⟩
  -- point for A
  obtain ⟨q₂, hq₂C, hq₂m, hq₂φ⟩ := de_cond_point P hint φ hφ hφi
    (Set.Icc qlo qhi ∩ {x | v ≤ f x})
    ((convex_Icc qlo qhi).inter (convex_halfSpace_ge (f := f) (by
      rw [hf]; constructor
      · intro x y; simp [Finset.sum_add_distrib]
      · intro c x; simp [Finset.mul_sum]) v))
    (isClosed_Icc.inter (isClosed_le continuous_const hfc)) μ A (fun h => absurd h hA0)
    (by
      rw [ae_restrict_iff' hAm]
      filter_upwards [hboxae] with x hx hxA
      exact ⟨hx, show v ≤ f x from le_of_lt hxA⟩)
  obtain ⟨q₁, hq₁C, hq₁m, hq₁φ⟩ := de_cond_point P hint φ hφ hφi
    (Set.Icc qlo qhi) (convex_Icc qlo qhi) isClosed_Icc μ Aᶜ (fun _ => hμI)
    (ae_restrict_of_ae hboxae)
  refine ⟨P.real Aᶜ, P.real A, q₁, q₂, measureReal_nonneg, hpA, by linarith, hq₁C, hq₂C.1,
    hq₂C.2, ?_⟩
  refine de_twoPoint_mem qlo qhi μ φ σ _ _ q₁ q₂ measureReal_nonneg measureReal_nonneg
    (by linarith) hq₁C hq₂C.1 ?_ ?_
  · intro i
    have h1 := congrFun hq₁m i
    have h2 := congrFun hq₂m i
    simp only [Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [h1, h2, eval_integral (fun j => (hint.integrableOn (s := Aᶜ)).eval j) i,
      eval_integral (fun j => (hint.integrableOn (s := A)).eval j) i, add_comm,
      integral_add_compl hAm ((hmean i).1)]
    exact (hmean i).2
  · intro l
    have := add_le_add (hq₁φ l) (hq₂φ l)
    rw [add_comm (∫ x in Aᶜ, φ l x ∂P), integral_add_compl hAm (hφi l)] at this
    exact this.trans (hdisp l).2

lemma de_bddAbove {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (σ : Fin p → ℝ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (U : Finset (Fin n)) :
    BddAbove ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ U, q i) (1 - ε)) ''
      momentAmbiguitySet qlo qhi μ φ σ) := by
  refine ⟨∑ i ∈ U, qhi i, ?_⟩
  rintro _ ⟨P, hP, rfl⟩
  haveI := hP.1
  exact de_var_le qlo qhi P hP.2.1 U (1 - ε) (by linarith) (by linarith)

lemma de_twoPoint_le_W {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (σ : Fin p → ℝ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (U : Finset (Fin n)) (P : Measure (Fin n → ℝ))
    (hP : P ∈ momentAmbiguitySet qlo qhi μ φ σ) :
    MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ U, q i) (1 - ε) ≤
      worstCaseVaR (momentAmbiguitySet qlo qhi μ φ σ) ε U :=
  le_csSup (de_bddAbove qlo qhi μ φ σ ε hε0 hε1 U) ⟨P, hP, rfl⟩

lemma de_W_union {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (σ : Fin p → ℝ) (ε : ℝ)
    (hqlo : ∀ i, 0 ≤ qlo i)
    (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (hφ : ∀ l, ConvexOn ℝ Set.univ (φ l))
    (hε0 : 0 < ε) (hε1 : ε < 1) (S T : Finset (Fin n)) :
    worstCaseVaR (momentAmbiguitySet qlo qhi μ φ σ) ε (S ∪ T) ≤
      worstCaseVaR (momentAmbiguitySet qlo qhi μ φ σ) ε S +
        worstCaseVaR (momentAmbiguitySet qlo qhi μ φ σ) ε T := by
  set Amb := momentAmbiguitySet qlo qhi μ φ σ with hAmb
  rcases Set.eq_empty_or_nonempty Amb with he | hne
  · unfold worstCaseVaR; rw [he]; simp
  unfold worstCaseVaR
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨P, hP, rfl⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨v, hv0, hv⟩ := exists_between hcon
  obtain ⟨p₁, p₂, q₁, q₂, h1, h2, h12, hq1, hq2, hv2, hmem⟩ :=
    de_exists_twoPoint qlo qhi μ φ σ ε hμ hφ hε0 hε1 P hP (S ∪ T) v hv
  have hS := (de_twoPoint_var_ge p₁ p₂ ε q₁ q₂ h1 h12 h2 hε0 hε1 S).trans
    (de_twoPoint_le_W qlo qhi μ φ σ ε hε0 hε1 S _ hmem)
  have hT := (de_twoPoint_var_ge p₁ p₂ ε q₁ q₂ h1 h12 h2 hε0 hε1 T).trans
    (de_twoPoint_le_W qlo qhi μ φ σ ε hε0 hε1 T _ hmem)
  have hu : ∑ i ∈ S ∪ T, q₂ i ≤ ∑ i ∈ S, q₂ i + ∑ i ∈ T, q₂ i := by
    rw [← Finset.sum_union_inter]
    have : 0 ≤ ∑ i ∈ S ∩ T, q₂ i :=
      Finset.sum_nonneg (fun i _ => (hqlo i).trans (hq2.1 i))
    linarith
  unfold worstCaseVaR at hS hT
  linarith

theorem demandEstimator_subadditive_core {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (σ : Fin p → ℝ) (ε Q : ℝ)
    (hqlo : ∀ i, 0 ≤ qlo i)
    (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (hφ : ∀ l, ConvexOn ℝ Set.univ (φ l))
    (hσ : ∀ l, φ l μ < σ l)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hQ : 0 < Q)
    (S T : Finset (Fin n)) :
    demandEstimator (momentAmbiguitySet qlo qhi μ φ σ) ε Q (S ∪ T) ≤
      demandEstimator (momentAmbiguitySet qlo qhi μ φ σ) ε Q S +
        demandEstimator (momentAmbiguitySet qlo qhi μ φ σ) ε Q T := by
  have hW := de_W_union qlo qhi μ φ σ ε hqlo hμ hφ hε0 hε1 S T
  set Amb := momentAmbiguitySet qlo qhi μ φ σ
  have hnn : ∀ U, 0 ≤ demandEstimator Amb ε Q U := by
    intro U; unfold demandEstimator; split_ifs
    · exact le_rfl
    · exact le_trans zero_le_one (le_max_right _ _)
  by_cases hS : S = ∅
  · subst hS; simp only [Finset.empty_union]; have := hnn ∅; linarith
  by_cases hT : T = ∅
  · subst hT; simp only [Finset.union_empty]; have := hnn ∅; linarith
  have hST : S ∪ T ≠ ∅ := by
    intro h; exact hS (Finset.union_eq_empty.mp h).1
  unfold demandEstimator
  rw [if_neg hST, if_neg hS, if_neg hT]
  have hc : ⌈worstCaseVaR Amb ε (S ∪ T) / Q⌉ ≤
      ⌈worstCaseVaR Amb ε S / Q⌉ + ⌈worstCaseVaR Amb ε T / Q⌉ := by
    refine le_trans (Int.ceil_mono ?_) (Int.ceil_add_le _ _)
    rw [← add_div]; exact div_le_div_of_nonneg_right hW hQ.le
  have a1 := le_max_left ⌈worstCaseVaR Amb ε S / Q⌉ 1
  have a2 := le_max_left ⌈worstCaseVaR Amb ε T / Q⌉ 1
  have b1 := le_max_right ⌈worstCaseVaR Amb ε S / Q⌉ 1
  have b2 := le_max_right ⌈worstCaseVaR Amb ε T / Q⌉ 1
  refine max_le ?_ ?_ <;> linarith

end DRCVRP.Moment

open DRCVRP.Moment


theorem solution {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (σ : Fin p → ℝ) (ε Q : ℝ)
    (hqlo : ∀ i, 0 ≤ qlo i)
    (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (hφ : ∀ l, ConvexOn ℝ Set.univ (φ l))
    (hσ : ∀ l, φ l μ < σ l)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hQ : 0 < Q)
    (S T : Finset (Fin n)) :
    demandEstimator (momentAmbiguitySet qlo qhi μ φ σ) ε Q (S ∪ T) ≤
      demandEstimator (momentAmbiguitySet qlo qhi μ φ σ) ε Q S +
        demandEstimator (momentAmbiguitySet qlo qhi μ φ σ) ε Q T := by
  exact demandEstimator_subadditive_core qlo qhi μ φ σ ε Q hqlo hμ hφ hσ hε0 hε1 hQ S T
