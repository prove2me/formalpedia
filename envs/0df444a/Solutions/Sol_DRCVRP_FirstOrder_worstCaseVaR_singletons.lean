-- Prove2me | solution 1 for DRCVRP.FirstOrder.worstCaseVaR_singletons
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T15:29:27.592845+00:00
-- url     : https://prove2.me/submissions/4358b211-d346-4c76-b69d-1db48ac52833

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_FirstOrder_AmbiguitySet
import Definitions.Def_DRCVRP_FirstOrder_ConvexProgram

open MeasureTheory


namespace DRCVRP.FirstOrder

def momentAmbiguitySet' {n p : ℕ} (qlo qhi μ : Fin n → ℝ) (φ : Fin p → (Fin n → ℝ) → ℝ)
    (σ : Fin p → ℝ) : Set (Measure (Fin n → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (Set.Icc qlo qhi) = 1 ∧
    (∀ i, Integrable (fun q => q i) P ∧ ∫ q, q i ∂P = μ i) ∧
    ∀ l, Integrable (φ l) P ∧ ∫ q, φ l q ∂P ≤ σ l}

noncomputable def twoPointMeasure' {n : ℕ} (p₁ p₂ : ℝ) (q₁ q₂ : Fin n → ℝ) :
    Measure (Fin n → ℝ) :=
  ENNReal.ofReal p₁ • Measure.dirac q₁ + ENNReal.ofReal p₂ • Measure.dirac q₂

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
    Integrable g (twoPointMeasure' p₁ p₂ q₁ q₂) ∧
      ∫ x, g x ∂(twoPointMeasure' p₁ p₂ q₁ q₂) = p₁ * g q₁ + p₂ * g q₂ := by
  have i1 : Integrable g (Measure.dirac q₁) := integrable_dirac (by simp)
  have i2 : Integrable g (Measure.dirac q₂) := integrable_dirac (by simp)
  have j1 : Integrable g (ENNReal.ofReal p₁ • Measure.dirac q₁) := i1.smul_measure (by simp)
  have j2 : Integrable g (ENNReal.ofReal p₂ • Measure.dirac q₂) := i2.smul_measure (by simp)
  refine ⟨j1.add_measure j2, ?_⟩
  unfold twoPointMeasure'
  rw [integral_add_measure j1 j2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]
  simp [smul_eq_mul]

lemma de_twoPoint_apply {n : ℕ} (p₁ p₂ : ℝ) (q₁ q₂ : Fin n → ℝ) (s : Set (Fin n → ℝ)) :
    twoPointMeasure' p₁ p₂ q₁ q₂ s =
      ENNReal.ofReal p₁ * s.indicator 1 q₁ + ENNReal.ofReal p₂ * s.indicator 1 q₂ := by
  unfold twoPointMeasure'
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply,
    Measure.dirac_apply]
  simp

lemma de_twoPoint_mem {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (σ : Fin p → ℝ) (p₁ p₂ : ℝ) (q₁ q₂ : Fin n → ℝ)
    (h1 : 0 ≤ p₁) (h2 : 0 ≤ p₂) (h12 : p₁ + p₂ = 1)
    (hq1 : q₁ ∈ Set.Icc qlo qhi) (hq2 : q₂ ∈ Set.Icc qlo qhi)
    (hm : ∀ i, p₁ * q₁ i + p₂ * q₂ i = μ i)
    (hs : ∀ l, p₁ * φ l q₁ + p₂ * φ l q₂ ≤ σ l) :
    twoPointMeasure' p₁ p₂ q₁ q₂ ∈ momentAmbiguitySet' qlo qhi μ φ σ := by
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
    ∑ i ∈ U, q₂ i ≤ MultistageStochastic.valueAtRisk (twoPointMeasure' p₁ p₂ q₁ q₂)
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
    (P : Measure (Fin n → ℝ)) (hP : P ∈ momentAmbiguitySet' qlo qhi μ φ σ)
    (U : Finset (Fin n)) (v : ℝ)
    (hv : v < MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ U, q i) (1 - ε)) :
    ∃ p₁ p₂ : ℝ, ∃ q₁ q₂ : Fin n → ℝ, 0 ≤ p₁ ∧ ε < p₂ ∧ p₁ + p₂ = 1 ∧
      q₁ ∈ Set.Icc qlo qhi ∧ q₂ ∈ Set.Icc qlo qhi ∧ v ≤ ∑ i ∈ U, q₂ i ∧
      twoPointMeasure' p₁ p₂ q₁ q₂ ∈ momentAmbiguitySet' qlo qhi μ φ σ := by
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
      momentAmbiguitySet' qlo qhi μ φ σ) := by
  refine ⟨∑ i ∈ U, qhi i, ?_⟩
  rintro _ ⟨P, hP, rfl⟩
  haveI := hP.1
  exact de_var_le qlo qhi P hP.2.1 U (1 - ε) (by linarith) (by linarith)

def phiFO {n p : ℕ} (μ : Fin n → ℝ) (Sfam : Fin p → Finset (Fin n)) :
    Fin p → (Fin n → ℝ) → ℝ :=
  fun l q => ∑ j ∈ Sfam l, |q j - μ j|

lemma fo_eq_mom {n p : ℕ} (qlo qhi μ : Fin n → ℝ) (Sfam : Fin p → Finset (Fin n))
    (ν : Fin p → ℝ) :
    firstOrderAmbiguitySet qlo qhi μ Sfam ν = momentAmbiguitySet' qlo qhi μ (phiFO μ Sfam) ν :=
  rfl

lemma phiFO_convex {n p : ℕ} (μ : Fin n → ℝ) (Sfam : Fin p → Finset (Fin n)) (l : Fin p) :
    ConvexOn ℝ Set.univ (phiFO μ Sfam l) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [phiFO, smul_eq_mul, Pi.add_apply, Pi.smul_apply, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have e : a * x j + b * y j - μ j = a * (x j - μ j) + b * (y j - μ j) := by
    linear_combination (μ j) * hab
  rw [e]
  calc |a * (x j - μ j) + b * (y j - μ j)| ≤ |a * (x j - μ j)| + |b * (y j - μ j)| :=
        abs_add_le _ _
    _ = a * |x j - μ j| + b * |y j - μ j| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

lemma qhat_nonneg {n : ℕ} (qlo qhi μ : Fin n → ℝ) (ε : ℝ)
    (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hε₀ : 0 < ε) (hε₁ : ε < 1) (j : Fin n) :
    0 ≤ qhat qlo qhi μ ε j := by
  unfold qhat
  refine le_min (by linarith [(hμ j).2]) (mul_nonneg (div_nonneg (by linarith) hε₀.le)
    (by linarith [(hμ j).1]))

lemma tp_bound {n p : ℕ} (qlo qhi μ : Fin n → ℝ) (Sfam : Fin p → Finset (Fin n))
    (ν : Fin p → ℝ) (ε : ℝ) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j)
    (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (p₁ p₂ : ℝ) (q₁ q₂ : Fin n → ℝ) (h1 : 0 ≤ p₁) (hp2 : ε < p₂) (h12 : p₁ + p₂ = 1)
    (hq1 : q₁ ∈ Set.Icc qlo qhi) (hq2 : q₂ ∈ Set.Icc qlo qhi)
    (hm : ∀ i, p₁ * q₁ i + p₂ * q₂ i = μ i)
    (hs : ∀ l, p₁ * phiFO μ Sfam l q₁ + p₂ * phiFO μ Sfam l q₂ ≤ ν l) :
    (∀ j, max (q₂ j - μ j) 0 ≤ qhat qlo qhi μ ε j) ∧
      ∀ l, 2 * ε * ∑ j ∈ Sfam l, |q₂ j - μ j| ≤ ν l := by
  have key : ∀ j, p₁ * (q₁ j - μ j) = - (p₂ * (q₂ j - μ j)) := by
    intro j; have := hm j; linear_combination this - (μ j) * h12
  constructor
  · intro j
    have hq2h := hq2.2 j
    have hq1l := hq1.1 j
    have hk := key j
    have hμj := hμ j
    refine max_le (le_min (by linarith) ?_) (qhat_nonneg qlo qhi μ ε hμ hε₀ hε₁ j)
    rw [div_mul_eq_mul_div, le_div_iff₀ hε₀]
    rcases le_or_gt (q₂ j - μ j) 0 with hd | hd
    · nlinarith
    · nlinarith
  · intro l
    have hs' := hs l
    have e : p₁ * phiFO μ Sfam l q₁ = p₂ * phiFO μ Sfam l q₂ := by
      simp only [phiFO, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← abs_of_nonneg h1, ← abs_mul, key j, abs_neg, abs_mul,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ p₂)]
    rw [e] at hs'
    have hφ : 0 ≤ phiFO μ Sfam l q₂ := Finset.sum_nonneg fun j _ => abs_nonneg _
    show 2 * ε * phiFO μ Sfam l q₂ ≤ ν l
    nlinarith

lemma dirac_mem {n p : ℕ} (qlo qhi μ : Fin n → ℝ) (Sfam : Fin p → Finset (Fin n))
    (ν : Fin p → ℝ) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hν : ∀ l, 0 < ν l) :
    twoPointMeasure' 1 0 μ μ ∈ firstOrderAmbiguitySet qlo qhi μ Sfam ν := by
  rw [fo_eq_mom]
  refine de_twoPoint_mem qlo qhi μ _ ν 1 0 μ μ (by norm_num) le_rfl (by norm_num)
    ⟨fun j => (hμ j).1.le, fun j => (hμ j).2.le⟩ ⟨fun j => (hμ j).1.le, fun j => (hμ j).2.le⟩
    (fun i => by ring) (fun l => ?_)
  simp [phiFO]; exact (hν l).le

lemma var_ub {n p : ℕ} (qlo qhi μ : Fin n → ℝ) (Sfam : Fin p → Finset (Fin n))
    (ν : Fin p → ℝ) (ε : ℝ) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (S : Finset (Fin n)) (B : ℝ)
    (hB : ∀ y : Fin n → ℝ, (∀ j, 0 ≤ y j) → (∀ j, y j ≤ qhat qlo qhi μ ε j) →
      (∀ l, 2 * ε * ∑ j ∈ Sfam l, y j ≤ ν l) → ∑ j ∈ S, y j ≤ B)
    (P : Measure (Fin n → ℝ)) (hP : P ∈ firstOrderAmbiguitySet qlo qhi μ Sfam ν) :
    MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε) ≤ ∑ j ∈ S, μ j + B := by
  by_contra hc
  push_neg at hc
  rw [fo_eq_mom] at hP
  obtain ⟨p₁, p₂, q₁, q₂, h1, hp2, h12, hq1, hq2, hv, hmem⟩ := de_exists_twoPoint qlo qhi μ
    (phiFO μ Sfam) ν ε hμ (phiFO_convex μ Sfam) hε₀ hε₁ P hP S
    ((MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε) +
      (∑ j ∈ S, μ j + B)) / 2) (by linarith)
  have hm : ∀ i, p₁ * q₁ i + p₂ * q₂ i = μ i := by
    intro i
    have := (hmem.2.2.1 i).2
    rwa [(de_twoPoint_integral p₁ p₂ h1 (by linarith) q₁ q₂ (fun q => q i)).2] at this
  have hs : ∀ l, p₁ * phiFO μ Sfam l q₁ + p₂ * phiFO μ Sfam l q₂ ≤ ν l := by
    intro l
    have := (hmem.2.2.2 l).2
    rwa [(de_twoPoint_integral p₁ p₂ h1 (by linarith) q₁ q₂ (phiFO μ Sfam l)).2] at this
  obtain ⟨hA, hBnd⟩ := tp_bound qlo qhi μ Sfam ν ε hμ hε₀ hε₁ p₁ p₂ q₁ q₂ h1 hp2 h12 hq1 hq2 hm hs
  have hy := hB (fun j => max (q₂ j - μ j) 0) (fun j => le_max_right _ _) hA (fun l => by
    refine le_trans ?_ (hBnd l)
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (by linarith)
    exact max_le (le_abs_self _) (abs_nonneg _))
  have : ∑ i ∈ S, q₂ i ≤ ∑ j ∈ S, μ j + ∑ j ∈ S, max (q₂ j - μ j) 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => by linarith [le_max_left (q₂ j - μ j) 0]
  linarith

lemma wc_ub {n p : ℕ} (qlo qhi μ : Fin n → ℝ) (Sfam : Fin p → Finset (Fin n))
    (ν : Fin p → ℝ) (ε : ℝ) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hν : ∀ l, 0 < ν l)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (S : Finset (Fin n)) (B : ℝ)
    (hB : ∀ y : Fin n → ℝ, (∀ j, 0 ≤ y j) → (∀ j, y j ≤ qhat qlo qhi μ ε j) →
      (∀ l, 2 * ε * ∑ j ∈ Sfam l, y j ≤ ν l) → ∑ j ∈ S, y j ≤ B) :
    worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S ≤ ∑ j ∈ S, μ j + B := by
  unfold worstCaseVaR
  refine csSup_le ⟨_, _, dirac_mem qlo qhi μ Sfam ν hμ hν, rfl⟩ ?_
  rintro _ ⟨P, hP, rfl⟩
  exact var_ub qlo qhi μ Sfam ν ε hμ hε₀ hε₁ S B hB P hP

lemma wc_lb_t {n p : ℕ} (qlo qhi μ : Fin n → ℝ) (Sfam : Fin p → Finset (Fin n))
    (ν : Fin p → ℝ) (ε : ℝ) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (S : Finset (Fin n)) (x : Fin n → ℝ)
    (hx0 : ∀ j, 0 ≤ x j) (hxq : ∀ j, x j ≤ qhat qlo qhi μ ε j)
    (hxs : ∀ l, 2 * ε * ∑ j ∈ Sfam l, x j ≤ ν l) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∑ j ∈ S, μ j + t * ∑ j ∈ S, x j ≤ worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S := by
  set D := ε + t * (1 - ε) with hD
  have hDp : 0 < D := by nlinarith
  have hD1 : D < 1 := by nlinarith
  have hne : (1 - ε) ≠ 0 := by intro h; linarith
  have hDne : D ≠ 0 := hDp.ne'
  set a := ε / (1 - ε) with ha
  have ha0 : 0 ≤ a := div_nonneg hε₀.le (by linarith)
  set p₂ := ε / D with hp₂
  set p₁ := t * (1 - ε) / D with hp₁
  have h12 : p₁ + p₂ = 1 := by
    rw [hp₁, hp₂, ← add_div, div_eq_one_iff_eq hDp.ne']; ring
  have h1 : 0 ≤ p₁ := div_nonneg (mul_nonneg ht0.le (by linarith)) hDp.le
  have hp2 : ε < p₂ := by rw [hp₂, lt_div_iff₀ hDp]; nlinarith
  set q₂ : Fin n → ℝ := fun j => μ j + t * x j with hq₂
  set q₁ : Fin n → ℝ := fun j => μ j - a * x j with hq₁
  have hxa : ∀ j, a * x j ≤ μ j - qlo j := by
    intro j
    have h := (hxq j).trans (min_le_right _ _)
    have : a * ((1 - ε) / ε * (μ j - qlo j)) = μ j - qlo j := by
      rw [ha]; field_simp
    calc a * x j ≤ a * ((1 - ε) / ε * (μ j - qlo j)) := mul_le_mul_of_nonneg_left h ha0
      _ = _ := this
  have hpa : p₁ * a = p₂ * t := by
    rw [hp₁, hp₂, ha]; field_simp
  have hmem : twoPointMeasure' p₁ p₂ q₁ q₂ ∈ firstOrderAmbiguitySet qlo qhi μ Sfam ν := by
    rw [fo_eq_mom]
    refine de_twoPoint_mem qlo qhi μ _ ν p₁ p₂ q₁ q₂ h1 (by linarith) h12 ?_ ?_ ?_ ?_
    · refine ⟨fun j => ?_, fun j => ?_⟩
      · simp only [hq₁]; linarith [hxa j]
      · simp only [hq₁]; nlinarith [hx0 j, (hμ j).2]
    · refine ⟨fun j => ?_, fun j => ?_⟩
      · simp only [hq₂]; nlinarith [hx0 j, (hμ j).1]
      · have h := (hxq j).trans (min_le_left _ _)
        simp only [hq₂]; nlinarith [hx0 j, mul_le_mul_of_nonneg_right ht1.le (hx0 j)]
    · intro i
      simp only [hq₁, hq₂]
      linear_combination (μ i) * h12 - (x i) * hpa
    · intro l
      have e1 : phiFO μ Sfam l q₁ = a * ∑ j ∈ Sfam l, x j := by
        simp only [phiFO, hq₁, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show μ j - a * x j - μ j = -(a * x j) by ring, abs_neg,
          abs_of_nonneg (mul_nonneg ha0 (hx0 j))]
      have e2 : phiFO μ Sfam l q₂ = t * ∑ j ∈ Sfam l, x j := by
        simp only [phiFO, hq₂, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show μ j + t * x j - μ j = t * x j by ring,
          abs_of_nonneg (mul_nonneg ht0.le (hx0 j))]
      rw [e1, e2, ← mul_assoc, hpa]
      have hX : 0 ≤ ∑ j ∈ Sfam l, x j := Finset.sum_nonneg fun j _ => hx0 j
      have hpt : p₂ * t ≤ ε := by
        have htD : t ≤ D := by rw [hD]; nlinarith
        rw [hp₂, div_mul_eq_mul_div, div_le_iff₀ hDp]
        exact mul_le_mul_of_nonneg_left htD hε₀.le
      nlinarith [hxs l]
  have hvar := de_twoPoint_var_ge p₁ p₂ ε q₁ q₂ h1 h12 hp2 hε₀ hε₁ S
  have hsum : ∑ i ∈ S, q₂ i = ∑ j ∈ S, μ j + t * ∑ j ∈ S, x j := by
    simp only [hq₂, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum] at hvar
  refine hvar.trans ?_
  unfold worstCaseVaR
  have hbdd := de_bddAbove qlo qhi μ (phiFO μ Sfam) ν ε hε₀ hε₁ S
  rw [← fo_eq_mom] at hbdd
  exact le_csSup hbdd ⟨_, hmem, rfl⟩

lemma wc_lb {n p : ℕ} (qlo qhi μ : Fin n → ℝ) (Sfam : Fin p → Finset (Fin n))
    (ν : Fin p → ℝ) (ε : ℝ) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (S : Finset (Fin n)) (x : Fin n → ℝ)
    (hx0 : ∀ j, 0 ≤ x j) (hxq : ∀ j, x j ≤ qhat qlo qhi μ ε j)
    (hxs : ∀ l, 2 * ε * ∑ j ∈ Sfam l, x j ≤ ν l) :
    ∑ j ∈ S, μ j + ∑ j ∈ S, x j ≤ worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S := by
  have h := fun t ht0 ht1 => wc_lb_t qlo qhi μ Sfam ν ε hμ hε₀ hε₁ S x hx0 hxq hxs t ht0 ht1
  have hT : 0 ≤ ∑ j ∈ S, x j := Finset.sum_nonneg fun j _ => hx0 j
  generalize ∑ j ∈ S, x j = T at h hT ⊢
  generalize worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S = W at h ⊢
  generalize ∑ j ∈ S, μ j = M at h ⊢
  by_contra hc
  push_neg at hc
  have h2 := h (1/2) (by norm_num) (by norm_num)
  have hTp : 0 < T := by
    rcases hT.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hc h2; linarith
  have hδ : 0 < M + T - W := by linarith
  have hq : 0 < (M + T - W) / (2 * T) := div_pos hδ (by linarith)
  have ht1 : max (1/2 : ℝ) (1 - (M + T - W) / (2 * T)) < 1 := max_lt (by norm_num) (by linarith)
  have ht0 : 0 < max (1/2 : ℝ) (1 - (M + T - W) / (2 * T)) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have h3 := h _ ht0 ht1
  have e : (1 - (M + T - W) / (2 * T)) * T = T - (M + T - W) / 2 := by field_simp
  have h4 : (1 - (M + T - W) / (2 * T)) * T ≤ max (1/2 : ℝ) (1 - (M + T - W) / (2 * T)) * T :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hT
  linarith

lemma blocks_split {n r : ℕ} (Sfam : Fin (r + 1) → Finset (Fin n))
    (hdisj : ∀ i i' : Fin r, i ≠ i' → Disjoint (Sfam i.castSucc) (Sfam i'.castSucc))
    (hcover : ∀ c : Fin n, ∃ i : Fin r, c ∈ Sfam i.castSucc) (S : Finset (Fin n))
    (y : Fin n → ℝ) : ∑ j ∈ S, y j = ∑ i : Fin r, ∑ j ∈ S ∩ Sfam i.castSucc, y j := by
  have hS : S = (Finset.univ : Finset (Fin r)).biUnion (fun i => S ∩ Sfam i.castSucc) := by
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_inter, true_and]
    constructor
    · intro hc; obtain ⟨i, hi⟩ := hcover c; exact ⟨i, hc, hi⟩
    · rintro ⟨i, hc, -⟩; exact hc
  conv_lhs => rw [hS]
  rw [Finset.sum_biUnion]
  intro i _ i' _ hii'
  exact Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right (hdisj i i' hii')

theorem blocks_core {n r : ℕ} (qlo qhi μ : Fin n → ℝ)
    (Sfam : Fin (r + 1) → Finset (Fin n)) (ν : Fin (r + 1) → ℝ) (ε : ℝ)
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hν : ∀ l, 0 < ν l)
    (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hdisj : ∀ i i' : Fin r, i ≠ i' → Disjoint (Sfam i.castSucc) (Sfam i'.castSucc))
    (hcover : ∀ c : Fin n, ∃ i : Fin r, c ∈ Sfam i.castSucc)
    (hlast : Sfam (Fin.last r) = Finset.univ) (S : Finset (Fin n)) :
    worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S =
      ∑ j ∈ S, μ j +
        min (ν (Fin.last r) / (2 * ε))
          (∑ i : Fin r,
            min (∑ j ∈ S ∩ Sfam i.castSucc, qhat qlo qhi μ ε j) (ν i.castSucc / (2 * ε))) := by
  have h2ε : 0 < 2 * ε := by linarith
  have hqh := qhat_nonneg qlo qhi μ ε hμ hε₀ hε₁
  have hV : ∀ l, 0 < ν l / (2 * ε) := fun l => div_pos (hν l) h2ε
  apply le_antisymm
  · apply wc_ub qlo qhi μ Sfam ν ε hμ hν hε₀ hε₁ S
    intro y hy0 hyq hys
    refine le_min ?_ ?_
    · rw [le_div_iff₀ h2ε]
      have h1 : ∑ j ∈ S, y j ≤ ∑ j ∈ Sfam (Fin.last r), y j := by
        rw [hlast]; exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => hy0 j)
      have := hys (Fin.last r)
      nlinarith
    · rw [blocks_split Sfam hdisj hcover S y]
      refine Finset.sum_le_sum fun i _ => le_min (Finset.sum_le_sum fun j _ => hyq j) ?_
      rw [le_div_iff₀ h2ε]
      have h1 : ∑ j ∈ S ∩ Sfam i.castSucc, y j ≤ ∑ j ∈ Sfam i.castSucc, y j :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun j _ _ => hy0 j)
      have := hys i.castSucc
      nlinarith
  · -- construction
    classical
    let b : Fin n → Fin r := fun j => (hcover j).choose
    have hb : ∀ j, j ∈ Sfam (b j).castSucc := fun j => (hcover j).choose_spec
    have hbi : ∀ j i, j ∈ Sfam i.castSucc → b j = i := by
      intro j i hj
      by_contra hne
      exact Finset.disjoint_left.1 (hdisj _ _ hne) (hb j) hj
    let Q : Fin r → ℝ := fun i => ∑ j ∈ S ∩ Sfam i.castSucc, qhat qlo qhi μ ε j
    let V : Fin (r + 1) → ℝ := fun l => ν l / (2 * ε)
    let Tm : Fin r → ℝ := fun i => min (Q i) (V i.castSucc)
    let lam : Fin r → ℝ := fun i => Tm i / Q i
    let Y : ℝ := ∑ i, Tm i
    let κ : ℝ := min Y (V (Fin.last r)) / Y
    have hQ0 : ∀ i, 0 ≤ Q i := fun i => Finset.sum_nonneg fun j _ => hqh j
    have hTm0 : ∀ i, 0 ≤ Tm i := fun i => le_min (hQ0 i) (hV _).le
    have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => hTm0 i
    have hlam0 : ∀ i, 0 ≤ lam i := fun i => div_nonneg (hTm0 i) (hQ0 i)
    have hlam1 : ∀ i, lam i ≤ 1 := fun i => div_le_one_of_le₀ (min_le_left _ _) (hQ0 i)
    have hκ0 : 0 ≤ κ := div_nonneg (le_min hY0 (hV _).le) hY0
    have hκ1 : κ ≤ 1 := div_le_one_of_le₀ (min_le_left _ _) hY0
    have hlamQ : ∀ i, lam i * Q i = Tm i := by
      intro i
      rcases (hQ0 i).lt_or_eq with h | h
      · exact div_mul_cancel₀ _ h.ne'
      · have : Tm i = 0 := by
          show min (Q i) (V i.castSucc) = 0
          rw [← h]; exact min_eq_left (hV _).le
        rw [this, ← h, mul_zero]
    have hκY : κ * Y = min Y (V (Fin.last r)) := by
      rcases hY0.lt_or_eq with h | h
      · exact div_mul_cancel₀ _ h.ne'
      · rw [← h, mul_zero]; exact (min_eq_left (hV _).le).symm
    let x : Fin n → ℝ := fun j => if j ∈ S then κ * lam (b j) * qhat qlo qhi μ ε j else 0
    have hx0 : ∀ j, 0 ≤ x j := by
      intro j; simp only [x]; split_ifs
      · exact mul_nonneg (mul_nonneg hκ0 (hlam0 _)) (hqh j)
      · exact le_rfl
    have hxq : ∀ j, x j ≤ qhat qlo qhi μ ε j := by
      intro j; simp only [x]; split_ifs
      · have : κ * lam (b j) ≤ 1 := by nlinarith [hκ0, hlam0 (b j), hκ1, hlam1 (b j)]
        nlinarith [hqh j, mul_nonneg hκ0 (hlam0 (b j))]
      · exact hqh j
    have hblock : ∀ i, ∑ j ∈ S ∩ Sfam i.castSucc, x j = κ * Tm i := by
      intro i
      rw [← hlamQ i]
      simp only [Q, Finset.mul_sum, ← mul_assoc]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_inter] at hj
      simp only [x, if_pos hj.1, hbi j i hj.2]
    have hSx : ∑ j ∈ S, x j = min Y (V (Fin.last r)) := by
      rw [blocks_split Sfam hdisj hcover S x, ← hκY, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hblock i
    have hoff : ∀ A : Finset (Fin n), ∑ j ∈ S ∩ A, x j = ∑ j ∈ A, x j := by
      intro A
      refine Finset.sum_subset Finset.inter_subset_right fun j hjA hj => ?_
      have : j ∉ S := fun h => hj (Finset.mem_inter.2 ⟨h, hjA⟩)
      simp [x, this]
    have hxs : ∀ l, 2 * ε * ∑ j ∈ Sfam l, x j ≤ ν l := by
      intro l
      rw [← le_div_iff₀' h2ε]
      induction l using Fin.lastCases with
      | last =>
        rw [hlast, ← hoff, Finset.inter_univ, hSx]; exact min_le_right _ _
      | cast i =>
        rw [← hoff, hblock i]
        calc κ * Tm i ≤ 1 * Tm i := mul_le_mul_of_nonneg_right hκ1 (hTm0 i)
          _ ≤ V i.castSucc := by rw [one_mul]; exact min_le_right _ _
    have := wc_lb qlo qhi μ Sfam ν ε hμ hε₀ hε₁ S x hx0 hxq hxs
    rw [hSx, min_comm] at this
    exact this

theorem singletons_core {n : ℕ} (qlo qhi μ : Fin n → ℝ)
    (Sfam : Fin (n + 1) → Finset (Fin n)) (ν : Fin (n + 1) → ℝ) (ε : ℝ)
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hν : ∀ l, 0 < ν l)
    (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hsing : ∀ i : Fin n, Sfam i.castSucc = {i})
    (hlast : Sfam (Fin.last n) = Finset.univ) (S : Finset (Fin n)) :
    worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S =
      ∑ j ∈ S, μ j +
        min (ν (Fin.last n) / (2 * ε))
          (∑ i ∈ S, min (qhat qlo qhi μ ε i) (ν i.castSucc / (2 * ε))) := by
  classical
  have hdisj : ∀ i i' : Fin n, i ≠ i' → Disjoint (Sfam i.castSucc) (Sfam i'.castSucc) := by
    intro i i' h; rw [hsing, hsing]; exact Finset.disjoint_singleton.2 h
  have hcover : ∀ c : Fin n, ∃ i : Fin n, c ∈ Sfam i.castSucc :=
    fun c => ⟨c, by rw [hsing]; exact Finset.mem_singleton_self c⟩
  rw [blocks_core qlo qhi μ Sfam ν ε hqlo hμ hν hε₀ hε₁ hdisj hcover hlast S]
  congr 2
  rw [← Finset.sum_subset (Finset.subset_univ S)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [hsing, Finset.inter_singleton_of_mem hi, Finset.sum_singleton]
  · intro i _ hi
    rw [hsing, Finset.inter_singleton_of_notMem hi, Finset.sum_empty]
    exact min_eq_left (div_pos (hν _) (by linarith)).le

end DRCVRP.FirstOrder

open DRCVRP.FirstOrder


theorem solution {n : ℕ} (qlo qhi μ : Fin n → ℝ)
    (Sfam : Fin (n + 1) → Finset (Fin n)) (ν : Fin (n + 1) → ℝ) (ε : ℝ)
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hν : ∀ l, 0 < ν l)
    (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hsing : ∀ i : Fin n, Sfam i.castSucc = {i})
    (hlast : Sfam (Fin.last n) = Finset.univ) (S : Finset (Fin n)) :
    worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S =
      ∑ j ∈ S, μ j +
        min (ν (Fin.last n) / (2 * ε))
          (∑ i ∈ S, min (qhat qlo qhi μ ε i) (ν i.castSucc / (2 * ε))) := by
  exact singletons_core qlo qhi μ Sfam ν ε hqlo hμ hν hε₀ hε₁ hsing hlast S
