-- Prove2me | solution 1 for DRCVRP.Marginal.worstCaseVaR_additive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T15:52:18.810891+00:00
-- url     : https://prove2.me/submissions/241cd33e-16a4-4809-9906-62ba9a565b12

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Marginal_WorstCaseVaR
import Definitions.Def_DRCVRP_Marginal_AmbiguitySets

open MeasureTheory


namespace DRCVRP.Marginal

section VaRBasics
variable {Ω : Type*} [MeasurableSpace Ω]

lemma wc_bddBelow (P : Measure Ω) (Y : Ω → ℝ) (α L : ℝ) (hα : 0 < α)
    (hL : ∀ᵐ ω ∂P, L ≤ Y ω) :
    BddBelow {y : ℝ | ENNReal.ofReal α ≤ P {ω | Y ω ≤ y}} := by
  refine ⟨L, fun y hy => ?_⟩
  by_contra hlt
  push_neg at hlt
  have h0 : P {ω | Y ω ≤ y} = 0 := by
    apply measure_mono_null (t := {ω | ¬ L ≤ Y ω})
    · intro ω hω; simp only [Set.mem_setOf_eq] at hω ⊢; linarith
    · exact ae_iff.mp hL
  simp only [Set.mem_setOf_eq, h0] at hy
  exact absurd hy (by simpa using hα)

lemma wc_var_le (P : Measure Ω) (Y : Ω → ℝ) (α L y : ℝ) (hα : 0 < α)
    (hL : ∀ᵐ ω ∂P, L ≤ Y ω) (hy : ENNReal.ofReal α ≤ P {ω | Y ω ≤ y}) :
    MultistageStochastic.valueAtRisk P Y α ≤ y :=
  csInf_le (wc_bddBelow P Y α L hα hL) hy

lemma wc_lt_of_lt_var (P : Measure Ω) (Y : Ω → ℝ) (α L y : ℝ) (hα : 0 < α)
    (hL : ∀ᵐ ω ∂P, L ≤ Y ω) (hy : y < MultistageStochastic.valueAtRisk P Y α) :
    P {ω | Y ω ≤ y} < ENNReal.ofReal α := by
  by_contra h
  push_neg at h
  have := wc_var_le P Y α L y hα hL h
  linarith

lemma wc_var_le_upper (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (α L U : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hL : ∀ᵐ ω ∂P, L ≤ Y ω) (hU : ∀ᵐ ω ∂P, Y ω ≤ U) :
    MultistageStochastic.valueAtRisk P Y α ≤ U := by
  apply wc_var_le P Y α L U hα hL
  have : P {ω | Y ω ≤ U} = 1 := by
    rw [measure_congr (ae_eq_univ.mpr ?_), measure_univ]
    have := ae_iff.mp hU
    convert this using 2
    ext ω; simp
  rw [this]; simpa using hα1

lemma wc_le_var (P : Measure Ω) (Y : Ω → ℝ) (α c : ℝ)
    (hne : ∃ y, ENNReal.ofReal α ≤ P {ω | Y ω ≤ y})
    (h : ∀ y, ENNReal.ofReal α ≤ P {ω | Y ω ≤ y} → c ≤ y) :
    c ≤ MultistageStochastic.valueAtRisk P Y α := by
  obtain ⟨y0, hy0⟩ := hne
  exact le_csInf ⟨y0, hy0⟩ h

end VaRBasics

section TwoPt
variable {n : ℕ}

noncomputable def twoPt (p : ℝ) (h ℓ : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  ENNReal.ofReal p • Measure.dirac h + ENNReal.ofReal (1 - p) • Measure.dirac ℓ

lemma twoPt_apply (p : ℝ) (h ℓ : Fin n → ℝ) (s : Set (Fin n → ℝ)) :
    twoPt p h ℓ s = ENNReal.ofReal p * s.indicator 1 h + ENNReal.ofReal (1 - p) * s.indicator 1 ℓ := by
  simp [twoPt, Measure.dirac_apply]

lemma twoPt_prob (p : ℝ) (h ℓ : Fin n → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (twoPt p h ℓ) := by
  constructor
  rw [twoPt_apply]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  simp

lemma twoPt_integrable (p : ℝ) (h ℓ : Fin n → ℝ) (f : (Fin n → ℝ) → ℝ) :
    Integrable f (twoPt p h ℓ) := by
  unfold twoPt
  refine Integrable.add_measure ?_ ?_
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp)

lemma twoPt_integral (p : ℝ) (h ℓ : Fin n → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (Fin n → ℝ) → ℝ) :
    ∫ q, f q ∂(twoPt p h ℓ) = p * f h + (1 - p) * f ℓ := by
  unfold twoPt
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure (by simp))
    ((integrable_dirac (by simp)).smul_measure (by simp))]
  rw [integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  rw [ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (by linarith)]
  simp [smul_eq_mul]

lemma var_twoPt_ge (p ε : ℝ) (h ℓ : Fin n → ℝ) (hε0 : 0 < ε) (hεp : ε < p) (hp1 : p ≤ 1)
    (Y : (Fin n → ℝ) → ℝ) :
    Y h ≤ MultistageStochastic.valueAtRisk (twoPt p h ℓ) Y (1 - ε) := by
  have hp0 : 0 ≤ p := by linarith
  apply wc_le_var
  · refine ⟨max (Y h) (Y ℓ), ?_⟩
    haveI := twoPt_prob p h ℓ hp0 hp1
    rw [twoPt_apply]
    simp only [Set.indicator, Set.mem_setOf_eq, le_max_left, le_max_right, if_true,
      Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_add hp0 (by linarith)]
    apply ENNReal.ofReal_le_ofReal; linarith
  · intro y hy
    by_contra hlt
    push_neg at hlt
    rw [twoPt_apply] at hy
    have h1 : ({ω | Y ω ≤ y} : Set (Fin n → ℝ)).indicator 1 h = (0 : ENNReal) := by
      simp [Set.indicator, not_le.mpr hlt]
    rw [h1, mul_zero, zero_add] at hy
    have h2 : ENNReal.ofReal (1 - p) * ({ω | Y ω ≤ y} : Set (Fin n → ℝ)).indicator 1 ℓ
        ≤ ENNReal.ofReal (1 - p) := by
      calc _ ≤ ENNReal.ofReal (1 - p) * 1 := by
            gcongr
            simp only [Set.indicator]; split_ifs <;> simp
        _ = _ := mul_one _
    have h3 := hy.trans h2
    rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at h3
    linarith

end TwoPt

section Reduce
variable {n : ℕ}

lemma twoPt_mem_marginal (qlo qhi μ : Fin n → ℝ) {p : Fin n → ℕ}
    (φ : (i : Fin n) → Fin (p i) → ℝ → ℝ) (σ : (i : Fin n) → Fin (p i) → ℝ)
    (r : ℝ) (h ℓ : Fin n → ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hh : h ∈ Set.Icc qlo qhi) (hl : ℓ ∈ Set.Icc qlo qhi)
    (hmean : ∀ i, r * h i + (1 - r) * ℓ i = μ i)
    (hφ : ∀ i l, r * φ i l (h i) + (1 - r) * φ i l (ℓ i) ≤ σ i l) :
    twoPt r h ℓ ∈ marginalSet qlo qhi μ φ σ := by
  refine ⟨twoPt_prob r h ℓ hr0 hr1, ?_, ?_, ?_⟩
  · rw [twoPt_apply]
    simp only [Set.indicator, hh, hl, if_true, Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_add hr0 (by linarith)]
    simp
  · intro i
    rw [twoPt_integral r h ℓ hr0 hr1]; exact hmean i
  · intro i l
    refine ⟨twoPt_integrable r h ℓ _, ?_⟩
    rw [twoPt_integral r h ℓ hr0 hr1]; exact hφ i l

lemma setInt_ge (P : Measure (Fin n → ℝ)) [IsFiniteMeasure P] (t : Set (Fin n → ℝ))
    (ht : MeasurableSet t) (f : (Fin n → ℝ) → ℝ) (hf : Integrable f P) (c : ℝ)
    (hc : ∀ᵐ q ∂P, q ∈ t → c ≤ f q) : P.real t * c ≤ ∫ q in t, f q ∂P := by
  have := setIntegral_mono_ae_restrict (integrableOn_const (C := c) (μ := P) (s := t))
    hf.integrableOn ((ae_restrict_iff' ht).mpr hc)
  simpa [setIntegral_const, smul_eq_mul] using this

lemma setInt_le (P : Measure (Fin n → ℝ)) [IsFiniteMeasure P] (t : Set (Fin n → ℝ))
    (ht : MeasurableSet t) (f : (Fin n → ℝ) → ℝ) (hf : Integrable f P) (c : ℝ)
    (hc : ∀ᵐ q ∂P, q ∈ t → f q ≤ c) : ∫ q in t, f q ∂P ≤ P.real t * c := by
  have := setIntegral_mono_ae_restrict hf.integrableOn (integrableOn_const (C := c) (μ := P) (s := t))
    ((ae_restrict_iff' ht).mpr hc)
  simpa [setIntegral_const, smul_eq_mul] using this

lemma box_ae (qlo qhi : Fin n → ℝ) (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (hbox : P (Set.Icc qlo qhi) = 1) : ∀ᵐ q ∂P, q ∈ Set.Icc qlo qhi :=
  (ae_iff_measure_eq measurableSet_Icc.nullMeasurableSet).mpr (by
    rw [measure_univ]; exact hbox)

lemma coord_integrable (qlo qhi : Fin n → ℝ) (P : Measure (Fin n → ℝ)) [IsProbabilityMeasure P]
    (hbox : P (Set.Icc qlo qhi) = 1) (i : Fin n) : Integrable (fun q : Fin n → ℝ => q i) P := by
  refine Integrable.of_bound (measurable_pi_apply i).aestronglyMeasurable (|qlo i| + |qhi i|) ?_
  filter_upwards [box_ae qlo qhi P hbox] with q hq
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (qlo i), hq.1 i, abs_nonneg (qhi i)]
  · linarith [le_abs_self (qhi i), hq.2 i, abs_nonneg (qlo i)]

lemma reduce (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    {p : Fin n → ℕ} (φ : (i : Fin n) → Fin (p i) → ℝ → ℝ) (σ : (i : Fin n) → Fin (p i) → ℝ)
    (hφ : ∀ i l, ConvexOn ℝ Set.univ (φ i l)) (hσ : ∀ i l, φ i l (μ i) < σ i l)
    (P : Measure (Fin n → ℝ)) (hP : P ∈ marginalSet qlo qhi μ φ σ) (S : Finset (Fin n)) (y : ℝ)
    (hy : y < MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) :
    ∃ r : ℝ, ∃ h ℓ : Fin n → ℝ, ε < r ∧ r < 1 ∧ h ∈ Set.Icc qlo qhi ∧ ℓ ∈ Set.Icc qlo qhi ∧
      (∀ i, r * h i + (1 - r) * ℓ i = μ i) ∧
      (∀ i l, r * φ i l (h i) + (1 - r) * φ i l (ℓ i) ≤ σ i l) ∧ y < ∑ i ∈ S, h i := by
  obtain ⟨hprob, hbox, hmean, hint⟩ := hP
  have hae := box_ae qlo qhi P hbox
  have hL : ∀ᵐ q ∂P, ∑ i ∈ S, qlo i ≤ ∑ i ∈ S, q i :=
    hae.mono (fun q hq => Finset.sum_le_sum fun i _ => hq.1 i)
  set V := MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε) with hV
  set y' := (y + V) / 2 with hy'
  have hyy' : y < y' := by rw [hy']; linarith
  have hy'V : y' < V := by rw [hy']; linarith
  have hlt := wc_lt_of_lt_var P (fun q => ∑ i ∈ S, q i) (1 - ε) _ y' (by linarith) hL hy'V
  have hcoord := coord_integrable qlo qhi P hbox
  have hsummeas : Measurable (fun q : Fin n → ℝ => ∑ i ∈ S, q i) :=
    Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  set A : Set (Fin n → ℝ) := {q | y' < ∑ i ∈ S, q i} with hA
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hsummeas
  have hAc : Aᶜ = {q | ∑ i ∈ S, q i ≤ y'} := by ext q; simp [hA]
  have hsumreal : P.real A + P.real Aᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hAm]; simp
  have hAcreal : P.real Aᶜ < 1 - ε := by
    rw [hAc]; exact ENNReal.toReal_lt_of_lt_ofReal hlt
  have hAc0 : 0 ≤ P.real Aᶜ := measureReal_nonneg
  rcases eq_or_lt_of_le (show P.real A ≤ 1 by linarith) with hp1 | hp1
  · -- the event has full probability
    have hAc00 : P Aᶜ = 0 := by
      have : P.real Aᶜ = 0 := by linarith
      exact (measureReal_eq_zero_iff).mp this
    have hAe : ∀ᵐ q ∂P, y' ≤ ∑ i ∈ S, q i := by
      rw [ae_iff]
      apply measure_mono_null _ hAc00
      intro q hq; simp only [Set.mem_setOf_eq, not_le] at hq
      simp [hA]; linarith
    have hint_sum : y' ≤ ∫ q, ∑ i ∈ S, q i ∂P := by
      have := integral_mono_ae (integrable_const y') (integrable_finsetSum S fun i _ => hcoord i) hAe
      simpa using this
    rw [integral_finsetSum S (fun i _ => hcoord i)] at hint_sum
    simp only [hmean] at hint_sum
    refine ⟨(1 + ε) / 2, μ, μ, by linarith, by linarith,
      ⟨fun i => (hμ i).1.le, fun i => (hμ i).2.le⟩, ⟨fun i => (hμ i).1.le, fun i => (hμ i).2.le⟩,
      fun i => by ring, fun i l => by linarith [hσ i l], by linarith⟩
  · set r := P.real A with hr
    have hr0 : ε < r := by linarith
    have hrpos : 0 < r := by linarith
    have hcpos : 0 < P.real Aᶜ := by linarith
    have hcr : P.real Aᶜ = 1 - r := by linarith
    refine ⟨r, fun i => r⁻¹ * ∫ q in A, q i ∂P, fun i => (P.real Aᶜ)⁻¹ * ∫ q in Aᶜ, q i ∂P,
      hr0, hp1, ?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro i
        have := setInt_ge P A hAm _ (hcoord i) (qlo i) (hae.mono fun q hq _ => hq.1 i)
        show qlo i ≤ r⁻¹ * ∫ q in A, q i ∂P
        rw [le_inv_mul_iff₀ hrpos]; linarith
      · intro i
        have := setInt_le P A hAm _ (hcoord i) (qhi i) (hae.mono fun q hq _ => hq.2 i)
        show r⁻¹ * ∫ q in A, q i ∂P ≤ qhi i
        rw [inv_mul_le_iff₀ hrpos]; linarith
    · constructor
      · intro i
        have := setInt_ge P Aᶜ hAm.compl _ (hcoord i) (qlo i) (hae.mono fun q hq _ => hq.1 i)
        show qlo i ≤ (P.real Aᶜ)⁻¹ * ∫ q in Aᶜ, q i ∂P
        rw [le_inv_mul_iff₀ hcpos]; linarith
      · intro i
        have := setInt_le P Aᶜ hAm.compl _ (hcoord i) (qhi i) (hae.mono fun q hq _ => hq.2 i)
        show (P.real Aᶜ)⁻¹ * ∫ q in Aᶜ, q i ∂P ≤ qhi i
        rw [inv_mul_le_iff₀ hcpos]; linarith
    · intro i
      rw [← hcr, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hrpos.ne', mul_inv_cancel₀ hcpos.ne',
        one_mul, one_mul, integral_add_compl hAm (hcoord i), hmean i]
    · intro i l
      have hcont : ContinuousOn (φ i l) Set.univ := (hφ i l).continuousOn isOpen_univ
      have hJ : ∀ t : Set (Fin n → ℝ), MeasurableSet t → 0 < P.real t →
          P.real t * φ i l ((P.real t)⁻¹ * ∫ q in t, q i ∂P) ≤ ∫ q in t, φ i l (q i) ∂P := by
        intro t ht htpos
        have h0 : P t ≠ 0 := by
          intro h0; rw [measureReal_def, h0] at htpos; simp at htpos
        have := (hφ i l).map_set_average_le hcont isClosed_univ h0 (measure_ne_top P t)
          (Filter.Eventually.of_forall fun _ => Set.mem_univ _) (hcoord i).integrableOn
          (hint i l).1.integrableOn
        rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul] at this
        calc P.real t * φ i l ((P.real t)⁻¹ * ∫ q in t, q i ∂P)
            ≤ P.real t * ((P.real t)⁻¹ * ∫ q in t, φ i l (q i) ∂P) :=
              mul_le_mul_of_nonneg_left this htpos.le
          _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ htpos.ne', one_mul]
      have h1 := hJ A hAm hrpos
      have h2 := hJ Aᶜ hAm.compl hcpos
      rw [hcr] at h2
      have h3 := integral_add_compl hAm (hint i l).1
      have h4 := (hint i l).2
      show r * φ i l (r⁻¹ * ∫ q in A, q i ∂P) +
        (1 - r) * φ i l ((P.real Aᶜ)⁻¹ * ∫ q in Aᶜ, q i ∂P) ≤ σ i l
      rw [hcr]
      linarith
    · have hge := setInt_ge P A hAm _ (integrable_finsetSum S fun i _ => hcoord i) y'
        (Filter.Eventually.of_forall fun q hq => le_of_lt hq)
      rw [integral_finsetSum S (fun i _ => (hcoord i).integrableOn)] at hge
      rw [← Finset.mul_sum]
      have : y' ≤ r⁻¹ * ∑ i ∈ S, ∫ q in A, q i ∂P := by
        rw [le_inv_mul_iff₀ hrpos]; linarith
      linarith

end Reduce

section Additive
variable {n : ℕ}

lemma shrink_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (r r' a b : ℝ)
    (hr0 : 0 ≤ r) (hrr : r ≤ r') (hr1 : r' < 1) :
    r * f a + (1 - r) * f ((r' * a + (1 - r') * b - r * a) / (1 - r)) ≤
      r' * f a + (1 - r') * f b := by
  have h1r : 0 < 1 - r := by linarith
  have hx : (r' * a + (1 - r') * b - r * a) / (1 - r) =
      ((r' - r) / (1 - r)) • a + ((1 - r') / (1 - r)) • b := by
    simp only [smul_eq_mul]; field_simp; ring
  have := hf.2 (Set.mem_univ a) (Set.mem_univ b)
    (div_nonneg (show 0 ≤ r' - r by linarith) h1r.le)
    (div_nonneg (show 0 ≤ 1 - r' by linarith) h1r.le) (by field_simp; ring)
  rw [hx]
  simp only [smul_eq_mul] at this ⊢
  have h2 := mul_le_mul_of_nonneg_left this h1r.le
  have h3 : (1 - r) * ((r' - r) / (1 - r) * f a + (1 - r') / (1 - r) * f b) =
      (r' - r) * f a + (1 - r') * f b := by field_simp
  linarith

lemma shrink_box (lo hi r r' a b : ℝ) (hr0 : 0 ≤ r) (hrr : r ≤ r') (hr1 : r' < 1)
    (ha : lo ≤ a ∧ a ≤ hi) (hb : lo ≤ b ∧ b ≤ hi) :
    lo ≤ (r' * a + (1 - r') * b - r * a) / (1 - r) ∧
      (r' * a + (1 - r') * b - r * a) / (1 - r) ≤ hi := by
  have h1r : 0 < 1 - r := by linarith
  constructor
  · rw [le_div_iff₀ h1r]
    nlinarith [mul_le_mul_of_nonneg_left ha.1 (show 0 ≤ r' - r by linarith),
      mul_le_mul_of_nonneg_left hb.1 (show 0 ≤ 1 - r' by linarith)]
  · rw [div_le_iff₀ h1r]
    nlinarith [mul_le_mul_of_nonneg_left ha.2 (show 0 ≤ r' - r by linarith),
      mul_le_mul_of_nonneg_left hb.2 (show 0 ≤ 1 - r' by linarith)]

lemma marginal_nonempty (qlo qhi μ : Fin n → ℝ) (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    {p : Fin n → ℕ} (φ : (i : Fin n) → Fin (p i) → ℝ → ℝ) (σ : (i : Fin n) → Fin (p i) → ℝ)
    (hσ : ∀ i l, φ i l (μ i) < σ i l) : (marginalSet qlo qhi μ φ σ).Nonempty :=
  ⟨_, twoPt_mem_marginal qlo qhi μ φ σ 1 μ μ zero_le_one le_rfl
    ⟨fun i => (hμ i).1.le, fun i => (hμ i).2.le⟩ ⟨fun i => (hμ i).1.le, fun i => (hμ i).2.le⟩
    (fun i => by ring) (fun i l => by linarith [hσ i l])⟩

lemma marginal_bdd (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    {p : Fin n → ℕ} (φ : (i : Fin n) → Fin (p i) → ℝ → ℝ) (σ : (i : Fin n) → Fin (p i) → ℝ)
    (S : Finset (Fin n)) :
    BddAbove ((fun P => MultistageStochastic.valueAtRisk P (fun q => ∑ i ∈ S, q i) (1 - ε)) ''
      marginalSet qlo qhi μ φ σ) := by
  refine ⟨∑ i ∈ S, qhi i, ?_⟩
  rintro _ ⟨P, hP, rfl⟩
  obtain ⟨hprob, hbox, -, -⟩ := hP
  have hae := box_ae qlo qhi P hbox
  exact wc_var_le_upper P _ (1 - ε) (∑ i ∈ S, qlo i) _ (by linarith) (by linarith)
    (hae.mono fun q hq => Finset.sum_le_sum fun i _ => hq.1 i)
    (hae.mono fun q hq => Finset.sum_le_sum fun i _ => hq.2 i)

theorem additive_core {n : ℕ}
    (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    {p : Fin n → ℕ} (φ : (i : Fin n) → Fin (p i) → ℝ → ℝ) (σ : (i : Fin n) → Fin (p i) → ℝ)
    (hφ : ∀ i l, ConvexOn ℝ Set.univ (φ i l)) (hσ : ∀ i l, φ i l (μ i) < σ i l)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    worstCaseVaR (marginalSet qlo qhi μ φ σ) ε S =
      ∑ i ∈ S, worstCaseVaR (marginalSet qlo qhi μ φ σ) ε {i} := by
  have hne := marginal_nonempty qlo qhi μ hμ φ σ hσ
  have hbdd := marginal_bdd qlo qhi μ ε hε₀ hε₁ φ σ
  -- any admissible two-point law gives a lower bound on the single-customer values
  have hsingle : ∀ (r : ℝ) (h ℓ : Fin n → ℝ), ε < r → r < 1 → h ∈ Set.Icc qlo qhi →
      ℓ ∈ Set.Icc qlo qhi → (∀ i, r * h i + (1 - r) * ℓ i = μ i) →
      (∀ i l, r * φ i l (h i) + (1 - r) * φ i l (ℓ i) ≤ σ i l) →
      ∀ T : Finset (Fin n), ∑ i ∈ T, h i ≤ worstCaseVaR (marginalSet qlo qhi μ φ σ) ε T := by
    intro r h ℓ hr hr1 hh hl hm hp T
    have hmem := twoPt_mem_marginal qlo qhi μ φ σ r h ℓ (by linarith) hr1.le hh hl hm hp
    exact (var_twoPt_ge r ε h ℓ hε₀ hr hr1.le (fun q => ∑ i ∈ T, q i)).trans
      (le_csSup (hbdd T) ⟨_, hmem, rfl⟩)
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro _ ⟨P, hP, rfl⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, h, ℓ, hr, hr1, hh, hl, hm, hp, hy⟩ :=
      reduce qlo qhi μ ε hε₀ hε₁ hμ φ σ hφ hσ P hP S _ hcon
    have : ∑ i ∈ S, h i ≤ ∑ i ∈ S, worstCaseVaR (marginalSet qlo qhi μ φ σ) ε {i} :=
      Finset.sum_le_sum fun i _ => by
        simpa using hsingle r h ℓ hr hr1 hh hl hm hp {i}
    linarith
  · apply le_of_forall_pos_le_add
    intro δ hδ
    have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    set d := δ / S.card with hd
    have hdpos : 0 < d := div_pos hδ hc
    have hex : ∀ i : Fin n, ∃ r : ℝ, ∃ h ℓ : Fin n → ℝ, ε < r ∧ r < 1 ∧ h ∈ Set.Icc qlo qhi ∧
        ℓ ∈ Set.Icc qlo qhi ∧ (∀ i, r * h i + (1 - r) * ℓ i = μ i) ∧
        (∀ i l, r * φ i l (h i) + (1 - r) * φ i l (ℓ i) ≤ σ i l) ∧
        worstCaseVaR (marginalSet qlo qhi μ φ σ) ε {i} - d < ∑ j ∈ ({i} : Finset (Fin n)), h j := by
      intro i
      obtain ⟨_, ⟨P, hP, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (hne.image _)
        (show worstCaseVaR (marginalSet qlo qhi μ φ σ) ε {i} - d <
          worstCaseVaR (marginalSet qlo qhi μ φ σ) ε {i} by linarith)
      exact reduce qlo qhi μ ε hε₀ hε₁ hμ φ σ hφ hσ P hP {i} _ hlt
    choose R H L hR hR1 hH hL hM hP hY using hex
    set r := S.inf' hS R with hrdef
    have hεr : ε < r := (Finset.lt_inf'_iff hS).mpr fun i _ => hR i
    have hrR : ∀ i ∈ S, r ≤ R i := fun i hi => Finset.inf'_le _ hi
    obtain ⟨i0, hi0⟩ := hS
    have hr1 : r < 1 := lt_of_le_of_lt (hrR i0 hi0) (hR1 i0)
    have hr0 : 0 ≤ r := by linarith
    let Hv : Fin n → ℝ := fun j => if j ∈ S then H j j else μ j
    let Lv : Fin n → ℝ := fun j => if j ∈ S then
      (R j * H j j + (1 - R j) * L j j - r * H j j) / (1 - r) else μ j
    have key := hsingle r Hv Lv hεr hr1 ?_ ?_ ?_ ?_ S
    · have hsum : ∑ i ∈ S, (worstCaseVaR (marginalSet qlo qhi μ φ σ) ε {i} - d) <
          ∑ i ∈ S, Hv i := by
        apply Finset.sum_lt_sum_of_nonempty ⟨i0, hi0⟩
        intro i hi
        have := hY i
        simp only [Finset.sum_singleton] at this
        simp only [Hv, hi, if_true]; exact this
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hd,
        mul_div_cancel₀ _ hc.ne'] at hsum
      linarith
    · constructor
      · intro j; simp only [Hv]; split_ifs
        · exact (hH j).1 j
        · exact (hμ j).1.le
      · intro j; simp only [Hv]; split_ifs
        · exact (hH j).2 j
        · exact (hμ j).2.le
    · have hb : ∀ j, qlo j ≤ Lv j ∧ Lv j ≤ qhi j := by
        intro j; simp only [Lv]; split_ifs with hj
        · exact shrink_box _ _ r (R j) _ _ hr0 (hrR j hj) (hR1 j) ⟨(hH j).1 j, (hH j).2 j⟩
            ⟨(hL j).1 j, (hL j).2 j⟩
        · exact ⟨(hμ j).1.le, (hμ j).2.le⟩
      exact ⟨fun j => (hb j).1, fun j => (hb j).2⟩
    · intro j; simp only [Hv, Lv]; split_ifs with hj
      · rw [hM j j]
        have h1r : (1 - r) ≠ 0 := (show 0 < 1 - r by linarith).ne'
        field_simp; ring
      · ring
    · intro j l; simp only [Hv, Lv]; split_ifs with hj
      · exact (shrink_convex _ (hφ j l) r (R j) _ _ hr0 (hrR j hj) (hR1 j)).trans (hP j j l)
      · linarith [hσ j l]

end Additive

end DRCVRP.Marginal

open DRCVRP.Marginal


theorem solution {n : ℕ}
    (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hqlo : ∀ i, 0 ≤ qlo i) (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    {p : Fin n → ℕ} (φ : (i : Fin n) → Fin (p i) → ℝ → ℝ) (σ : (i : Fin n) → Fin (p i) → ℝ)
    (hφ : ∀ i l, ConvexOn ℝ Set.univ (φ i l)) (hσ : ∀ i l, φ i l (μ i) < σ i l)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    worstCaseVaR (marginalSet qlo qhi μ φ σ) ε S =
      ∑ i ∈ S, worstCaseVaR (marginalSet qlo qhi μ φ σ) ε {i} := by
  exact additive_core qlo qhi μ ε hε₀ hε₁ hμ φ σ hφ hσ S hS
