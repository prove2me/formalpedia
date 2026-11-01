-- Prove2me | solution 1 for ESAxioms.Characterization.lemma_A3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:14:32.70819+00:00
-- url     : https://prove2.me/submissions/7ef35f1a-900a-49f4-ab63-620106687d16

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxP1Aux

open ESAxioms.Characterization

variable {Ω : Type*} [MeasurableSpace Ω]

local notation "F" => TailRiskSharing.VaRConv.distFn

lemma VaR_eq (P : Measure Ω) (q : ℝ) (X : Ω → ℝ) :
    VaR P q X = sInf {x | q ≤ F P X x} := by
  simp [VaR, TailRiskSharing.VaRConv.VaRL]

lemma distFn_eq_cdf (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (x : ℝ) : F P X x = cdf (P.map X) x := by
  have _hpm : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [cdf_eq_real, map_measureReal_apply hX measurableSet_Iic]
  rfl

lemma distFn_mono (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) :
    Monotone (F P X) := by
  intro x y hxy
  rw [distFn_eq_cdf P X hX, distFn_eq_cdf P X hX]
  exact (cdf (P.map X)).mono hxy

lemma distFn_top (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) :
    Tendsto (F P X) atTop (𝓝 1) := by
  have : F P X = cdf (P.map X) := funext (distFn_eq_cdf P X hX)
  have _hpm : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [this]; exact tendsto_cdf_atTop _

lemma distFn_bot (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) :
    Tendsto (F P X) atBot (𝓝 0) := by
  have : F P X = cdf (P.map X) := funext (distFn_eq_cdf P X hX)
  have _hpm : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [this]; exact tendsto_cdf_atBot _

lemma distFn_rc (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (x : ℝ) : ContinuousWithinAt (F P X) (Set.Ici x) x := by
  have : F P X = cdf (P.map X) := funext (distFn_eq_cdf P X hX)
  rw [this]; exact (cdf (P.map X)).right_continuous x

lemma set_nonempty (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (q : ℝ) (hq : q < 1) : {x | q ≤ F P X x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((distFn_top P X hX).eventually (eventually_gt_nhds hq)).exists
  exact ⟨x, hx.le⟩

lemma set_bdd (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (q : ℝ) (hq : 0 < q) : BddBelow {x | q ≤ F P X x} := by
  obtain ⟨x0, hx0⟩ := eventually_atBot.mp ((distFn_bot P X hX).eventually (eventually_lt_nhds hq))
  refine ⟨x0, fun y hy => ?_⟩
  by_contra h
  push Not at h
  have := hx0 y h.le
  simp only [Set.mem_setOf_eq] at hy
  linarith

/-- Galois connection: `VaR_q(X) ≤ x ↔ q ≤ F_X(x)`. -/
lemma VaR_le_iff (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (q : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (x : ℝ) : VaR P q X ≤ x ↔ q ≤ F P X x := by
  rw [VaR_eq]
  have hne := set_nonempty P X hX q hq.2
  have hbdd := set_bdd P X hX q hq.1
  constructor
  · intro h
    have hgt : ∀ y, x < y → q ≤ F P X y := by
      intro y hy
      obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne (lt_of_le_of_lt h hy)
      exact le_trans hz (distFn_mono P X hX hzy.le)
    have hrc := ((distFn_rc P X hX x).mono Set.Ioi_subset_Ici_self).tendsto
    exact ge_of_tendsto hrc (eventually_nhdsWithin_of_forall fun y hy => hgt y hy)
  · intro h
    exact csInf_le hbdd h

lemma lt_VaR_iff (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (q : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (x : ℝ) : x < VaR P q X ↔ F P X x < q := by
  rw [← not_le, VaR_le_iff P X hX q hq, not_le]

lemma VaR_mono_q (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) :
    MonotoneOn (fun q => VaR P q X) (Set.Ioo (0:ℝ) 1) := by
  intro q hq q' hq' hqq'
  simp only
  rw [VaR_le_iff P X hX q hq]
  exact le_trans hqq' ((VaR_le_iff P X hX q' hq' _).mp le_rfl)

lemma VaR_mono_X (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Measurable X)
    (hY : Measurable Y) (hXY : ∀ ω, X ω ≤ Y ω) (q : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) :
    VaR P q X ≤ VaR P q Y := by
  rw [VaR_le_iff P X hX q hq]
  have h1 := (VaR_le_iff P Y hY q hq _).mp le_rfl
  refine le_trans h1 ?_
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  exact le_trans (hXY ω) hω

lemma VaR_LI (P : Measure Ω) (X Y : Ω → ℝ) (h : SameLaw P X Y) (q : ℝ) :
    VaR P q X = VaR P q Y := by
  rw [VaR_eq, VaR_eq]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq]
  rw [h x]

/-- Lower semicontinuity of `VaR_q` under pointwise convergence. -/
lemma VaR_lsc (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hξ : ∀ k, Measurable (ξ k)) (hX : Measurable X)
    (hconv : ∀ ω, Tendsto (fun k => ξ k ω) atTop (𝓝 (X ω)))
    (q : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (x : ℝ) (hx : x < VaR P q X) :
    ∀ᶠ k in atTop, x < VaR P q (ξ k) := by
  set y := (x + VaR P q X) / 2 with hy
  have hxy : x < y := by rw [hy]; linarith
  have hFy : F P X y < q := (lt_VaR_iff P X hX q hq y).mp (by rw [hy]; linarith)
  set E : ℕ → Set Ω := fun k => {ω | ξ k ω ≤ x} ∩ {ω | y < X ω} with hE
  set G : ℕ → Set Ω := fun n => ⋃ k ≥ n, E k with hG
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (measurableSet_le (hξ k) measurable_const).inter (measurableSet_lt measurable_const hX)
  have hGm : ∀ n, MeasurableSet (G n) := fun n =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hEm k
  have hGanti : Antitone G := by
    intro n m hnm ω hω
    simp only [hG, Set.mem_iUnion] at hω ⊢
    obtain ⟨k, hk, hω⟩ := hω
    exact ⟨k, le_trans hnm hk, hω⟩
  have hGinter : (⋂ n, G n) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_forall]
    by_cases hXω : y < X ω
    · have hev := (hconv ω).eventually (eventually_gt_nhds (lt_trans hxy hXω))
      obtain ⟨n, hn⟩ := eventually_atTop.mp hev
      refine ⟨n, ?_⟩
      simp only [hG, hE, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, not_exists, not_and]
      intro k hk h1
      linarith [hn k hk]
    · refine ⟨0, ?_⟩
      simp only [hG, hE, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, not_exists, not_and]
      intro k _ _ h2
      exact hXω h2
  have htend : Tendsto (fun n => P (G n)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := P) (fun n => (hGm n).nullMeasurableSet) hGanti
      ⟨0, measure_ne_top _ _⟩
    rw [hGinter, measure_empty] at this
    exact this
  have htend' : Tendsto (fun n => P.real (G n)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend
    simpa [Function.comp_def, measureReal_def] using this
  have hev := htend'.eventually (eventually_lt_nhds (sub_pos.mpr hFy))
  filter_upwards [hev] with k hk
  rw [lt_VaR_iff P (ξ k) (hξ k) q hq x]
  have hsub : {ω | ξ k ω ≤ x} ⊆ {ω | X ω ≤ y} ∪ G k := by
    intro ω hω
    by_cases h : X ω ≤ y
    · exact Or.inl h
    · right
      simp only [hG, hE, Set.mem_iUnion]
      push Not at h
      exact ⟨k, le_rfl, hω, h⟩
  have h1 : F P (ξ k) x ≤ P.real ({ω | X ω ≤ y} ∪ G k) :=
    measureReal_mono hsub (measure_ne_top _ _)
  have h2 : P.real ({ω | X ω ≤ y} ∪ G k) ≤ P.real {ω | X ω ≤ y} + P.real (G k) :=
    measureReal_union_le _ _
  have h3 : F P X y = P.real {ω | X ω ≤ y} := rfl
  linarith

lemma VaR_aemeas (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    AEMeasurable (fun q => VaR P q X) (volume.restrict (Set.Ioo a b)) := by
  apply aemeasurable_restrict_of_monotoneOn measurableSet_Ioo
  intro q hq q' hq' h
  exact VaR_mono_q P X hX ⟨by linarith [hq.1], by linarith [hq.2]⟩
    ⟨by linarith [hq'.1], by linarith [hq'.2]⟩ h

/-- Quantile transform: under Lebesgue measure on `(0,1)`, `q ↦ VaR_q(X)` has the law of `X`. -/
lemma map_VaR (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X) :
    (volume.restrict (Set.Ioo (0:ℝ) 1)).map (fun q => VaR P q X) = P.map X := by
  have hQ := VaR_aemeas P X hX 0 1 le_rfl le_rfl
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply_of_aemeasurable hQ measurableSet_Iic, Measure.restrict_apply' measurableSet_Ioo,
    Measure.map_apply hX measurableSet_Iic]
  have hset : (fun q => VaR P q X) ⁻¹' Set.Iic a ∩ Set.Ioo 0 1 = Set.Ioo 0 1 ∩ Set.Iic (F P X a) := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (VaR_le_iff P X hX q h2 a).mp h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨(VaR_le_iff P X hX q h2 a).mpr h1, h2⟩
  rw [hset]
  have hRHS : P (X ⁻¹' Set.Iic a) = ENNReal.ofReal (F P X a) := by
    rw [← ofReal_measureReal (μ := P) (s := X ⁻¹' Set.Iic a)]; rfl
  rw [hRHS]
  have h0 : 0 ≤ F P X a := measureReal_nonneg
  have h1 : F P X a ≤ 1 := by
    have := measureReal_mono (μ := P) (Set.subset_univ {ω | X ω ≤ a}) (measure_ne_top _ _)
    rwa [probReal_univ] at this
  rcases lt_or_eq_of_le h1 with hlt | heq
  · have : Set.Ioo (0:ℝ) 1 ∩ Set.Iic (F P X a) = Set.Ioc 0 (F P X a) := by
      ext q; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
    rw [this, Real.volume_Ioc, sub_zero]
  · have : Set.Ioo (0:ℝ) 1 ∩ Set.Iic (F P X a) = Set.Ioo 0 1 := by
      rw [heq]; exact Set.inter_eq_left.mpr (fun q hq => Set.mem_Iic.mpr hq.2.le)
    rw [this, Real.volume_Ioo, heq]; simp

lemma VaR_integrableOn (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : X ∈ L1 P) :
    IntegrableOn (fun q => VaR P q X) (Set.Ioo (0:ℝ) 1) := by
  have hQ := VaR_aemeas P X hX.1 0 1 le_rfl le_rfl
  have h1 : Integrable id (P.map X) :=
    (integrable_map_measure aestronglyMeasurable_id hX.1.aemeasurable).mpr hX.2
  rw [← map_VaR P X hX.1] at h1
  exact (integrable_map_measure aestronglyMeasurable_id hQ).mp h1

lemma VaR_integrableOn' (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : X ∈ L1 P)
    (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) :
    IntegrableOn (fun q => VaR P q X) (Set.Ioo p 1) :=
  (VaR_integrableOn P X hX).mono_set (Set.Ioo_subset_Ioo_left hp.1.le)

lemma VaR_P (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) :
    AxiomP (L1 P) (VaR P p) := by
  intro ξ X hξ hX hconv L hL
  by_contra h
  push Not at h
  have hev := VaR_lsc P ξ X (fun k => (hξ k).1) hX.1 hconv p hp ((L + VaR P p X) / 2)
    (by linarith)
  have := ge_of_tendsto hL (hev.mono fun k hk => hk.le)
  linarith

lemma ES_M (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) :
    AxiomM (L1 P) (ES P p) := by
  intro X hX Y hY hXY
  unfold ES
  have hpos : 0 ≤ (1 - p)⁻¹ := inv_nonneg.mpr (by linarith [hp.2])
  apply mul_le_mul_of_nonneg_left _ hpos
  apply setIntegral_mono_on (VaR_integrableOn' P X hX p hp) (VaR_integrableOn' P Y hY p hp)
    measurableSet_Ioo
  intro q hq
  exact VaR_mono_X P X Y hX.1 hY.1 hXY q ⟨lt_trans hp.1 hq.1, hq.2⟩

lemma ES_LI (P : Measure Ω) (p : ℝ) : AxiomLI P (L1 P) (ES P p) := by
  intro X _ Y _ hXY
  unfold ES
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro q _
  exact VaR_LI P X Y hXY q

lemma ES_P (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) :
    AxiomP (L1 P) (ES P p) := by
  intro ξ X hξ hX hconv L hL
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  set c := VaR P p X - 1 with hc
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (VaR_lsc P ξ X (fun k => (hξ k).1) hX.1 hconv p hp c (by rw [hc]; linarith))
  have hIoo : ∀ q ∈ Set.Ioo p 1, q ∈ Set.Ioo (0:ℝ) 1 := fun q hq => ⟨lt_trans hp.1 hq.1, hq.2⟩
  -- lower bounds on (p,1)
  have hlowξ : ∀ k, ∀ q ∈ Set.Ioo p 1, c ≤ VaR P q (ξ (k + K)) := by
    intro k q hq
    exact le_trans (hK (k + K) (by omega)).le
      (VaR_mono_q P (ξ (k+K)) (hξ _).1 hp (hIoo q hq) hq.1.le)
  have hlowX : ∀ q ∈ Set.Ioo p 1, c ≤ VaR P q X := by
    intro q hq
    have := VaR_mono_q P X hX.1 hp (hIoo q hq) hq.1.le
    simp only at this
    linarith
  set μ := volume.restrict (Set.Ioo p 1) with hμ
  set G : ℕ → ℝ → ℝ := fun k q => min (VaR P q (ξ (k + K))) (VaR P q X) with hG
  have hXint : Integrable (fun q => VaR P q X) μ := VaR_integrableOn' P X hX p hp
  have hξint : ∀ k, Integrable (fun q => VaR P q (ξ (k + K))) μ :=
    fun k => VaR_integrableOn' P _ (hξ _) p hp
  have hbound : Integrable (fun q => |c| + |VaR P q X|) μ :=
    (integrable_const _).add hXint.abs
  have hGmeas : ∀ k, AEStronglyMeasurable (G k) μ := fun k =>
    ((VaR_aemeas P (ξ (k+K)) (hξ _).1 p 1 hp.1.le le_rfl).min
      (VaR_aemeas P X hX.1 p 1 hp.1.le le_rfl)).aestronglyMeasurable
  have hGbound : ∀ k, ∀ᵐ q ∂μ, ‖G k q‖ ≤ |c| + |VaR P q X| := by
    intro k
    rw [hμ, ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun q hq => ?_
    have h1 := hlowξ k q hq
    have h2 := hlowX q hq
    simp only [hG, Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · have : c ≤ min (VaR P q (ξ (k + K))) (VaR P q X) := le_min h1 h2
      linarith [neg_abs_le c, abs_nonneg (VaR P q X)]
    · have : min (VaR P q (ξ (k + K))) (VaR P q X) ≤ VaR P q X := min_le_right _ _
      linarith [le_abs_self (VaR P q X), abs_nonneg c]
  have hGlim : ∀ᵐ q ∂μ, Tendsto (fun k => G k q) atTop (𝓝 (VaR P q X)) := by
    rw [hμ, ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun q hq => ?_
    rw [tendsto_order]
    constructor
    · intro a ha
      have hev := VaR_lsc P ξ X (fun k => (hξ k).1) hX.1 hconv q (hIoo q hq) a ha
      have hev' : ∀ᶠ k in atTop, a < VaR P q (ξ (k + K)) :=
        (tendsto_add_atTop_nat K).eventually hev
      filter_upwards [hev'] with k hk
      exact lt_min hk ha
    · intro a ha
      exact Eventually.of_forall fun k => lt_of_le_of_lt (min_le_right _ _) ha
  have hDCT := tendsto_integral_of_dominated_convergence _ hGmeas hbound hGbound hGlim
  have hle : ∀ k, ∫ q, G k q ∂μ ≤ (1 - p) * ES P p (ξ (k + K)) := by
    intro k
    unfold ES
    rw [← mul_assoc, mul_inv_cancel₀ hp1.ne', one_mul]
    have hGint : Integrable (G k) μ := Integrable.mono' hbound (hGmeas k) (hGbound k)
    exact integral_mono hGint (hξint k) (fun q => min_le_left _ _)
  have hlimR : Tendsto (fun k => (1 - p) * ES P p (ξ (k + K))) atTop (𝓝 ((1 - p) * L)) :=
    (hL.comp (tendsto_add_atTop_nat K)).const_mul (1 - p)
  have hfin : ∫ q, VaR P q X ∂μ ≤ (1 - p) * L := le_of_tendsto_of_tendsto' hDCT hlimR hle
  unfold ES
  rw [← hμ]
  calc (1 - p)⁻¹ * ∫ q, VaR P q X ∂μ ≤ (1 - p)⁻¹ * ((1 - p) * L) :=
        mul_le_mul_of_nonneg_left hfin (inv_nonneg.mpr hp1.le)
    _ = L := by field_simp

theorem prop1 (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (AxiomM (L1 P) (ES P p) ∧ AxiomLI P (L1 P) (ES P p) ∧ AxiomP (L1 P) (ES P p)) ∧
    (AxiomM (L1 P) (VaR P p) ∧ AxiomLI P (L1 P) (VaR P p) ∧ AxiomP (L1 P) (VaR P p)) := by
  refine ⟨⟨ES_M P p hp, ES_LI P p, ES_P P p hp⟩, ⟨?_, ?_, VaR_P P p hp⟩⟩
  · intro X hX Y hY hXY
    exact VaR_mono_X P X Y hX.1 hY.1 hXY p hp
  · intro X _ Y _ hXY
    exact VaR_LI P X Y hXY p

end ESAxP1Aux

namespace ESAxAtomless

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Halving inside a set: subsets of arbitrarily small positive probability. -/
lemma exists_small_sub (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (S : Set Ω) (hS : MeasurableSet S)
    (hSpos : 0 < P.real S) (n : ℕ) :
    ∃ B ⊆ S, MeasurableSet B ∧ 0 < P.real B ∧ P.real B ≤ (1/2 : ℝ) ^ n * P.real S := by
  induction n with
  | zero => exact ⟨S, le_rfl, hS, hSpos, by simp⟩
  | succ n ih =>
    obtain ⟨B, hBS, hB, hpos, hle⟩ := ih
    have hB' : 0 < P B := by
      rw [measureReal_def] at hpos
      exact ENNReal.toReal_pos_iff.mp hpos |>.1
    obtain ⟨t, htB, ht, ht0, htlt⟩ := hP B hB hB'
    have ht0' : 0 < P.real t := by
      rw [measureReal_def]; exact ENNReal.toReal_pos ht0.ne' (measure_ne_top _ _)
    have htlt' : P.real t < P.real B := by
      rw [measureReal_def, measureReal_def]
      exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr htlt
    have hd : P.real (B \ t) = P.real B - P.real t := measureReal_sdiff htB ht
    by_cases h : P.real t ≤ P.real B / 2
    · refine ⟨t, htB.trans hBS, ht, ht0', ?_⟩
      rw [pow_succ]; nlinarith
    · refine ⟨B \ t, Set.diff_subset.trans hBS, hB.diff ht, by rw [hd]; linarith, ?_⟩
      rw [hd, pow_succ]; push Not at h; nlinarith

lemma exists_small_sub' (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (S : Set Ω) (hS : MeasurableSet S)
    (hSpos : 0 < P.real S) (ε : ℝ) (hε : 0 < ε) :
    ∃ B ⊆ S, MeasurableSet B ∧ 0 < P.real B ∧ P.real B ≤ ε := by
  have hS1 : P.real S ≤ 1 := by
    have := measureReal_mono (μ := P) (Set.subset_univ S) (measure_ne_top _ _)
    rwa [probReal_univ] at this
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2:ℝ) < 1)
  obtain ⟨B, hBS, hB, hpos, hle⟩ := exists_small_sub P hP S hS hSpos n
  refine ⟨B, hBS, hB, hpos, ?_⟩
  have : (1/2:ℝ) ^ n * P.real S ≤ (1/2) ^ n := by
    have : 0 ≤ (1/2:ℝ) ^ n := by positivity
    nlinarith
  linarith

lemma step_exists (P : Measure Ω) [IsProbabilityMeasure P] (S : Set Ω) (t : ℝ) (T : Set Ω) :
    ∃ U : Set Ω, (MeasurableSet T → T ⊆ S → P.real T ≤ t →
      (MeasurableSet U ∧ U ⊆ S \ T ∧ P.real T + P.real U ≤ t ∧
        ∀ V, MeasurableSet V → V ⊆ S \ T → P.real T + P.real V ≤ t → P.real V ≤ 2 * P.real U)) := by
  by_cases hT : MeasurableSet T ∧ T ⊆ S ∧ P.real T ≤ t
  · obtain ⟨hTm, hTS, hTt⟩ := hT
    set adm : Set ℝ := {r | ∃ U, MeasurableSet U ∧ U ⊆ S \ T ∧ P.real T + P.real U ≤ t ∧
      r = P.real U} with hadm
    have hne : adm.Nonempty := ⟨0, ∅, MeasurableSet.empty, Set.empty_subset _, by simpa using hTt,
      by simp⟩
    have hbdd : BddAbove adm := ⟨1, fun r ⟨U, _, _, _, hr⟩ => by
      rw [hr]
      have := measureReal_mono (μ := P) (Set.subset_univ U) (measure_ne_top _ _)
      rwa [probReal_univ] at this⟩
    set s := sSup adm with hs
    have hle : ∀ V, MeasurableSet V → V ⊆ S \ T → P.real T + P.real V ≤ t → P.real V ≤ s :=
      fun V hV hVS hVt => le_csSup hbdd ⟨V, hV, hVS, hVt, rfl⟩
    have hs0 : 0 ≤ s := le_csSup_of_le hbdd ⟨∅, MeasurableSet.empty, Set.empty_subset _,
      by simpa using hTt, by simp⟩ le_rfl
    rcases eq_or_lt_of_le hs0 with h0 | hpos
    · refine ⟨∅, fun _ _ _ => ⟨MeasurableSet.empty, Set.empty_subset _, by simpa using hTt, ?_⟩⟩
      intro V hV hVS hVt
      have := hle V hV hVS hVt
      simp; linarith
    · obtain ⟨r, ⟨U, hU, hUS, hUt, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hne (half_lt_self hpos)
      refine ⟨U, fun _ _ _ => ⟨hU, hUS, hUt, ?_⟩⟩
      intro V hV hVS hVt
      have := hle V hV hVS hVt
      linarith
  · exact ⟨∅, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hT⟩

/-- Sierpiński's theorem: in an atomless probability space every value in `[0, ℙ(S)]` is the
probability of a measurable subset of `S`. -/
theorem sierpinski (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (S : Set Ω) (hS : MeasurableSet S)
    (t : ℝ) (ht0 : 0 ≤ t) (htS : t ≤ P.real S) :
    ∃ T ⊆ S, MeasurableSet T ∧ P.real T = t := by
  choose g hg using step_exists P S t
  let T : ℕ → Set Ω := fun n => Nat.rec ∅ (fun _ Tn => Tn ∪ g Tn) n
  have hT0 : T 0 = ∅ := rfl
  have hTs : ∀ n, T (n + 1) = T n ∪ g (T n) := fun n => rfl
  have inv : ∀ n, MeasurableSet (T n) ∧ T n ⊆ S ∧ P.real (T n) ≤ t := by
    intro n
    induction n with
    | zero => rw [hT0]; exact ⟨MeasurableSet.empty, Set.empty_subset _, by simpa using ht0⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨hU, hUS, hUt, -⟩ := hg (T n) h1 h2 h3
      have hdisj : Disjoint (T n) (g (T n)) :=
        Set.disjoint_left.mpr fun ω h1 h2 => (hUS h2).2 h1
      rw [hTs]
      refine ⟨h1.union hU, Set.union_subset h2 (hUS.trans Set.diff_subset), ?_⟩
      rw [measureReal_union hdisj hU]; exact hUt
  have hadd : ∀ n, P.real (T (n+1)) = P.real (T n) + P.real (g (T n)) := by
    intro n
    obtain ⟨h1, h2, h3⟩ := inv n
    obtain ⟨hU, hUS, -, -⟩ := hg (T n) h1 h2 h3
    have hdisj : Disjoint (T n) (g (T n)) :=
      Set.disjoint_left.mpr fun ω h1 h2 => (hUS h2).2 h1
    rw [hTs, measureReal_union hdisj hU]
  have hmono : Monotone T := monotone_nat_of_le_succ fun n => by
    rw [hTs]; exact Set.subset_union_left
  set Tinf := ⋃ n, T n with hTinf
  have hTinfm : MeasurableSet Tinf := MeasurableSet.iUnion fun n => (inv n).1
  have hTinfS : Tinf ⊆ S := Set.iUnion_subset fun n => (inv n).2.1
  have hlim : Tendsto (fun n => P.real (T n)) atTop (𝓝 (P.real Tinf)) := by
    have := tendsto_measure_iUnion_atTop (μ := P) hmono
    have := (ENNReal.tendsto_toReal (measure_ne_top P Tinf)).comp this
    simpa [Function.comp_def, measureReal_def] using this
  have hTinft : P.real Tinf ≤ t := le_of_tendsto' hlim fun n => (inv n).2.2
  refine ⟨Tinf, hTinfS, hTinfm, ?_⟩
  by_contra hne
  have hlt : P.real Tinf < t := lt_of_le_of_ne hTinft hne
  -- increments tend to zero
  have hinc : Tendsto (fun n => P.real (g (T n))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => P.real (T (n+1)) - P.real (T n)) atTop
        (𝓝 (P.real Tinf - P.real Tinf)) :=
      (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
    rw [sub_self] at h1
    refine h1.congr fun n => ?_
    show P.real (T (n+1)) - P.real (T n) = P.real (g (T n))
    rw [hadd n]; ring
  have hrest : 0 < P.real (S \ Tinf) := by
    rw [measureReal_sdiff hTinfS hTinfm]; linarith
  obtain ⟨V, hVS, hV, hVpos, hVle⟩ :=
    exists_small_sub' P hP (S \ Tinf) (hS.diff hTinfm) hrest (t - P.real Tinf) (by linarith)
  have hbound : ∀ n, P.real V ≤ 2 * P.real (g (T n)) := by
    intro n
    obtain ⟨h1, h2, h3⟩ := inv n
    obtain ⟨-, -, -, hmax⟩ := hg (T n) h1 h2 h3
    apply hmax V hV
    · intro ω hω
      exact ⟨(hVS hω).1, fun h => (hVS hω).2 (Set.mem_iUnion.mpr ⟨n, h⟩)⟩
    · have : P.real (T n) ≤ P.real Tinf :=
        measureReal_mono (Set.subset_iUnion T n) (measure_ne_top _ _)
      linarith
  have h2 : Tendsto (fun n => 2 * P.real (g (T n))) atTop (𝓝 0) := by
    simpa using hinc.const_mul 2
  have := ge_of_tendsto h2 (Eventually.of_forall hbound)
  linarith

end ESAxAtomless

namespace ESAxA3Aux

open ESAxioms.Characterization ESAxP1Aux ESAxAtomless

variable {Ω : Type*} [MeasurableSpace Ω]

local notation "F" => TailRiskSharing.VaRConv.distFn

/-- Two positive-probability pieces `C ⊆ A`, `D ⊆ Aᶜ` with `X ≤ y` on `C` and `X > y` on `D`
contradict the tail-event condition. -/
lemma tail_contra (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (A C D : Set Ω)
    (y : ℝ) (hC : MeasurableSet C) (hD : MeasurableSet D) (hCA : C ⊆ A) (hDA : D ⊆ Aᶜ)
    (hCy : ∀ ω ∈ C, X ω ≤ y) (hDy : ∀ ω ∈ D, y < X ω) (hCpos : 0 < P.real C)
    (hDpos : 0 < P.real D)
    (htail : ∀ᵐ z ∂(P.prod P), z.1 ∈ A → z.2 ∉ A → X z.2 ≤ X z.1) : False := by
  rw [ae_iff] at htail
  have hsub : C ×ˢ D ⊆ {z : Ω × Ω | ¬(z.1 ∈ A → z.2 ∉ A → X z.2 ≤ X z.1)} := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩ h
    exact absurd (h (hCA ha) (hDA hb)) (not_le.mpr (lt_of_le_of_lt (hCy a ha) (hDy b hb)))
  have h0 := measure_mono_null hsub htail
  rw [Measure.prod_prod] at h0
  have hC' : P C ≠ 0 := by
    intro h; rw [measureReal_def, h] at hCpos; simp at hCpos
  have hD' : P D ≠ 0 := by
    intro h; rw [measureReal_def, h] at hDpos; simp at hDpos
  exact mul_ne_zero hC' hD' h0

lemma measureReal_pos_of_ne (P : Measure Ω) [IsProbabilityMeasure P] (S : Set Ω)
    (h : ¬ P S = 0) : 0 < P.real S := by
  rw [measureReal_def]; exact ENNReal.toReal_pos h (measure_ne_top _ _)

theorem lemmaA3 (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (X : Ω → ℝ) (hX : Measurable X) :
    (∀ A : Set Ω, MeasurableSet A →
      (IsPTailEvent P p X A ↔
        (P.real A = 1 - p ∧ {ω | VaR P p X < X ω} ≤ᵐ[P] A ∧ A ≤ᵐ[P] {ω | VaR P p X ≤ X ω}))) ∧
    ∃ A : Set Ω, IsPTailEvent P p X A := by
  set x := VaR P p X with hx
  -- the (⇐) direction, used twice
  have back : ∀ A : Set Ω, MeasurableSet A → P.real A = 1 - p →
      {ω | x < X ω} ≤ᵐ[P] A → A ≤ᵐ[P] {ω | x ≤ X ω} → IsPTailEvent P p X A := by
    intro A hA hPA h1 h2
    refine ⟨⟨hA, by rw [hPA]; linarith [hp.2], by rw [hPA]; linarith [hp.1], ?_⟩, hPA⟩
    have g1 : ∀ᵐ ω ∂P, ω ∈ A → x ≤ X ω := h2
    have g2 : ∀ᵐ ω ∂P, ω ∉ A → X ω ≤ x := by
      filter_upwards [h1] with ω hω hωA
      by_contra hc
      push Not at hc
      exact hωA (hω hc)
    have k1 := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae g1
    have k2 := (Measure.quasiMeasurePreserving_snd (μ := P) (ν := P)).ae g2
    filter_upwards [k1, k2] with z hz1 hz2 hzA hzA'
    exact le_trans (hz2 hzA') (hz1 hzA)
  refine ⟨fun A hA => ⟨fun hT => ?_, fun ⟨h1, h2, h3⟩ => back A hA h1 h2 h3⟩, ?_⟩
  · obtain ⟨⟨_, hpos, hlt1, htail⟩, hPA⟩ := hT
    refine ⟨hPA, ?_, ?_⟩
    · -- {X > x} ⊆ A a.e.
      show ∀ᵐ ω ∂P, ω ∈ {ω | x < X ω} → ω ∈ A
      rw [ae_iff]
      by_contra hne
      have hset : {ω | ¬(ω ∈ {ω | x < X ω} → ω ∈ A)} = Aᶜ ∩ {ω | x < X ω} := by
        ext ω; simp [and_comm]
      rw [hset] at hne
      have hU : Aᶜ ∩ {ω | x < X ω} = ⋃ n : ℕ, Aᶜ ∩ {ω | x + 1 / ((n:ℝ) + 1) < X ω} := by
        ext ω; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · rintro ⟨h1, h2⟩
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h2)
          exact ⟨n, h1, by linarith⟩
        · rintro ⟨n, h1, h2⟩
          have : 0 < 1 / ((n:ℝ) + 1) := by positivity
          exact ⟨h1, by linarith⟩
      rw [hU] at hne
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ¬ P (Aᶜ ∩ {ω | x + 1 / ((n:ℝ) + 1) < X ω}) = 0 := by
        by_contra hall
        push Not at hall
        exact hne (measure_iUnion_null hall)
      set y := x + 1 / ((n:ℝ) + 1) with hy
      have hxy : x < y := by rw [hy]; have : 0 < 1 / ((n:ℝ) + 1) := by positivity
                             linarith
      have hD := measureReal_pos_of_ne P _ hn
      -- P(A ∩ {X ≤ y}) > 0
      have hC : 0 < P.real (A ∩ {ω | X ω ≤ y}) := by
        by_contra hC0
        push Not at hC0
        have hC0' : P.real (A ∩ {ω | X ω ≤ y}) = 0 := le_antisymm hC0 measureReal_nonneg
        have hFy : p ≤ F P X y := (VaR_le_iff P X hX p hp y).mp hxy.le
        -- {X ≤ y} ⊆ Aᶜ ∪ (A ∩ {X ≤ y}), so F(y) ≤ P(Aᶜ ∩ {X ≤ y}) + 0
        have hm1 : P.real {ω | X ω ≤ y} ≤ P.real (Aᶜ ∩ {ω | X ω ≤ y}) +
            P.real (A ∩ {ω | X ω ≤ y}) := by
          calc P.real {ω | X ω ≤ y} ≤ P.real ((Aᶜ ∩ {ω | X ω ≤ y}) ∪ (A ∩ {ω | X ω ≤ y})) :=
                measureReal_mono (fun ω hω => by
                  by_cases h : ω ∈ A
                  · exact Or.inr ⟨h, hω⟩
                  · exact Or.inl ⟨h, hω⟩) (measure_ne_top _ _)
            _ ≤ _ := measureReal_union_le _ _
        have hdisj : Disjoint (Aᶜ ∩ {ω | X ω ≤ y}) (Aᶜ ∩ {ω | y < X ω}) :=
          Set.disjoint_left.mpr fun ω h1 h2 => by
            simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at h1 h2; linarith [h1.2, h2.2]
        have hm2 : P.real (Aᶜ ∩ {ω | X ω ≤ y}) + P.real (Aᶜ ∩ {ω | y < X ω}) ≤ P.real Aᶜ := by
          rw [← measureReal_union hdisj (hA.compl.inter (measurableSet_lt measurable_const hX))]
          exact measureReal_mono (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
            (measure_ne_top _ _)
        have hAc : P.real Aᶜ = p := by rw [probReal_compl_eq_one_sub hA, hPA]; ring
        have : F P X y = P.real {ω | X ω ≤ y} := rfl
        linarith
      exact tail_contra P X A (A ∩ {ω | X ω ≤ y}) (Aᶜ ∩ {ω | y < X ω}) y
        (hA.inter (measurableSet_le hX measurable_const))
        (hA.compl.inter (measurableSet_lt measurable_const hX))
        Set.inter_subset_left Set.inter_subset_left (fun ω h => h.2) (fun ω h => h.2) hC hD htail
    · -- A ⊆ {X ≥ x} a.e.
      show ∀ᵐ ω ∂P, ω ∈ A → ω ∈ {ω | x ≤ X ω}
      rw [ae_iff]
      by_contra hne
      have hset : {ω | ¬(ω ∈ A → ω ∈ {ω | x ≤ X ω})} = A ∩ {ω | X ω < x} := by
        ext ω; simp
      rw [hset] at hne
      have hU : A ∩ {ω | X ω < x} = ⋃ n : ℕ, A ∩ {ω | X ω ≤ x - 1 / ((n:ℝ) + 1)} := by
        ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · rintro ⟨h1, h2⟩
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h2)
          exact ⟨n, h1, by linarith⟩
        · rintro ⟨n, h1, h2⟩
          have : 0 < 1 / ((n:ℝ) + 1) := by positivity
          exact ⟨h1, by linarith⟩
      rw [hU] at hne
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ¬ P (A ∩ {ω | X ω ≤ x - 1 / ((n:ℝ) + 1)}) = 0 := by
        by_contra hall
        push Not at hall
        exact hne (measure_iUnion_null hall)
      set y := x - 1 / ((n:ℝ) + 1) with hy
      have hxy : y < x := by rw [hy]; have : 0 < 1 / ((n:ℝ) + 1) := by positivity
                             linarith
      have hC := measureReal_pos_of_ne P _ hn
      have hFy : F P X y < p := (lt_VaR_iff P X hX p hp y).mp hxy
      have hD : 0 < P.real (Aᶜ ∩ {ω | y < X ω}) := by
        by_contra hD0
        push Not at hD0
        -- Aᶜ ⊆ {X ≤ y} ∪ (Aᶜ ∩ {X > y})
        have hm1 : P.real Aᶜ ≤ P.real {ω | X ω ≤ y} + P.real (Aᶜ ∩ {ω | y < X ω}) := by
          calc P.real Aᶜ ≤ P.real ({ω | X ω ≤ y} ∪ (Aᶜ ∩ {ω | y < X ω})) :=
                measureReal_mono (fun ω hω => by
                  by_cases h : X ω ≤ y
                  · exact Or.inl h
                  · push Not at h; exact Or.inr ⟨hω, h⟩) (measure_ne_top _ _)
            _ ≤ _ := measureReal_union_le _ _
        have hAc : P.real Aᶜ = p := by rw [probReal_compl_eq_one_sub hA, hPA]; ring
        have : F P X y = P.real {ω | X ω ≤ y} := rfl
        linarith
      exact tail_contra P X A (A ∩ {ω | X ω ≤ y}) (Aᶜ ∩ {ω | y < X ω}) y
        (hA.inter (measurableSet_le hX measurable_const))
        (hA.compl.inter (measurableSet_lt measurable_const hX))
        Set.inter_subset_left Set.inter_subset_left (fun ω h => h.2) (fun ω h => h.2) hC hD htail
  · -- existence
    set G := {ω | x < X ω} with hG
    set E := {ω | X ω = x} with hE
    have hGm : MeasurableSet G := measurableSet_lt measurable_const hX
    have hEm : MeasurableSet E := measurableSet_eq_fun hX measurable_const
    have hFx : p ≤ F P X x := (VaR_le_iff P X hX p hp x).mp le_rfl
    have hPG : P.real G = 1 - F P X x := by
      have : G = {ω | X ω ≤ x}ᶜ := by ext ω; simp [hG]
      rw [this, probReal_compl_eq_one_sub (measurableSet_le hX measurable_const)]; rfl
    -- P(X < x) ≤ p
    have hlt : P.real {ω | X ω < x} ≤ p := by
      have hU : {ω | X ω < x} = ⋃ n : ℕ, {ω | X ω ≤ x - 1 / ((n:ℝ) + 2)} := by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · intro h
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
          refine ⟨n, ?_⟩
          have : 1 / ((n:ℝ) + 2) ≤ 1 / ((n:ℝ) + 1) :=
            one_div_le_one_div_of_le (by positivity) (by linarith)
          linarith
        · rintro ⟨n, h⟩
          have : 0 < 1 / ((n:ℝ) + 2) := by positivity
          linarith
      have hmono : Monotone (fun n : ℕ => {ω | X ω ≤ x - 1 / ((n:ℝ) + 2)}) := by
        intro n m hnm ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        have : 1 / ((m:ℝ) + 2) ≤ 1 / ((n:ℝ) + 2) :=
          one_div_le_one_div_of_le (by positivity) (by
            have : (n:ℝ) ≤ m := by exact_mod_cast hnm
            linarith)
        linarith
      have hlim := tendsto_measure_iUnion_atTop (μ := P) hmono
      have hlim' := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp hlim
      rw [← hU] at hlim'
      have hle : ∀ n : ℕ, (ENNReal.toReal ∘ (P ∘ fun n : ℕ => {ω | X ω ≤ x - 1 / ((n:ℝ) + 2)})) n ≤ p := by
        intro n
        have hyx : x - 1 / ((n:ℝ) + 2) < x := by
          have : 0 < 1 / ((n:ℝ) + 2) := by positivity
          linarith
        have := (lt_VaR_iff P X hX p hp _).mp hyx
        exact this.le
      have := le_of_tendsto' hlim' hle
      simpa [measureReal_def] using this
    have hGE : P.real (G ∪ E) = 1 - P.real {ω | X ω < x} := by
      have : G ∪ E = {ω | X ω < x}ᶜ := by
        ext ω; simp only [hG, hE, Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
        constructor
        · rintro (h | h)
          · exact h.le
          · exact h.ge
        · intro h; rcases eq_or_lt_of_le h with h | h
          · exact Or.inr h.symm
          · exact Or.inl h
      rw [this, probReal_compl_eq_one_sub (measurableSet_lt hX measurable_const)]
    have hdisj : Disjoint G E := Set.disjoint_left.mpr fun ω h1 h2 => by
      simp only [hG, hE, Set.mem_setOf_eq] at h1 h2; linarith
    have hGE' : P.real (G ∪ E) = P.real G + P.real E := measureReal_union hdisj hEm
    obtain ⟨T, hTE, hTm, hPT⟩ := sierpinski P hP E hEm (1 - p - P.real G)
      (by rw [hPG]; linarith) (by linarith)
    refine ⟨G ∪ T, back _ (hGm.union hTm) ?_ ?_ ?_⟩
    · have hdisj' : Disjoint G T := hdisj.mono_right hTE
      rw [measureReal_union hdisj' hTm, hPT]; ring
    · exact Eventually.of_forall fun ω hω => Or.inl hω
    · refine Eventually.of_forall fun ω hω => ?_
      rcases hω with h | h
      · exact (show x < X ω from h).le
      · exact (show X ω = x from hTE h).ge

end ESAxA3Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (X : Ω → ℝ) (hX : Measurable X) :
    (∀ A : Set Ω, MeasurableSet A →
      (ESAxioms.Characterization.IsPTailEvent P p X A ↔
        (P.real A = 1 - p ∧ {ω | ESAxioms.Characterization.VaR P p X < X ω} ≤ᵐ[P] A ∧
          A ≤ᵐ[P] {ω | ESAxioms.Characterization.VaR P p X ≤ X ω}))) ∧
    ∃ A : Set Ω, ESAxioms.Characterization.IsPTailEvent P p X A :=
  ESAxA3Aux.lemmaA3 P hP p hp X hX
