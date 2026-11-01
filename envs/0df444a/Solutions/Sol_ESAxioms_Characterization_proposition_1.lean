-- Prove2me | solution 1 for ESAxioms.Characterization.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T07:08:52.456929+00:00
-- url     : https://prove2.me/submissions/22595e07-7ec5-4136-bdfa-47198d057bc3

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

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (ESAxioms.Characterization.AxiomM (ESAxioms.Characterization.L1 P) (ESAxioms.Characterization.ES P p) ∧
      ESAxioms.Characterization.AxiomLI P (ESAxioms.Characterization.L1 P) (ESAxioms.Characterization.ES P p) ∧
      ESAxioms.Characterization.AxiomP (ESAxioms.Characterization.L1 P) (ESAxioms.Characterization.ES P p)) ∧
    (ESAxioms.Characterization.AxiomM (ESAxioms.Characterization.L1 P) (ESAxioms.Characterization.VaR P p) ∧
      ESAxioms.Characterization.AxiomLI P (ESAxioms.Characterization.L1 P) (ESAxioms.Characterization.VaR P p) ∧
      ESAxioms.Characterization.AxiomP (ESAxioms.Characterization.L1 P) (ESAxioms.Characterization.VaR P p)) :=
  ESAxP1Aux.prop1 P p hp
