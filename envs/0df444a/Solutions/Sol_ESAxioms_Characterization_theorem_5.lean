-- Prove2me | solution 1 for ESAxioms.Characterization.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:06:08.218601+00:00
-- url     : https://prove2.me/submissions/c89d0412-898d-49c1-924c-17c2a82a0077

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


namespace ESAxUnif

open ESAxAtomless

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Dyadic nested family: `fam H n k` has probability `min (k/2ⁿ) 1`. -/
noncomputable def fam (H : Set Ω → Set Ω) : ℕ → ℕ → Set Ω
  | 0, k => if k = 0 then ∅ else Set.univ
  | n + 1, j => if j % 2 = 0 then fam H n (j / 2)
      else fam H n (j / 2) ∪ H (fam H n (j / 2 + 1) \ fam H n (j / 2))

section defs
variable (H : Set Ω → Set Ω)

/-- The uniform variable: the smallest dyadic level set containing `ω`. -/
noncomputable def Uf (ω : Ω) : ℝ := sInf {d : ℝ | ∃ n k : ℕ, d = (k:ℝ) / 2 ^ n ∧ ω ∈ fam H n k}

lemma Uset_ne (ω : Ω) : {d : ℝ | ∃ n k : ℕ, d = (k:ℝ) / 2 ^ n ∧ ω ∈ fam H n k}.Nonempty :=
  ⟨1, 0, 1, by simp, by simp [fam]⟩

lemma Uset_bdd (ω : Ω) : BddBelow {d : ℝ | ∃ n k : ℕ, d = (k:ℝ) / 2 ^ n ∧ ω ∈ fam H n k} :=
  ⟨0, fun d ⟨n, k, hd, _⟩ => by rw [hd]; positivity⟩

lemma Uf_nonneg (ω : Ω) : 0 ≤ Uf H ω :=
  le_csInf (Uset_ne H ω) fun d ⟨n, k, hd, _⟩ => by rw [hd]; positivity

lemma Uf_le_one (ω : Ω) : Uf H ω ≤ 1 :=
  csInf_le (Uset_bdd H ω) ⟨0, 1, by simp, by simp [fam]⟩

lemma Uf_lt_iff (ω : Ω) (a : ℝ) :
    Uf H ω < a ↔ ∃ n k : ℕ, (k:ℝ) / 2 ^ n < a ∧ ω ∈ fam H n k := by
  unfold Uf
  rw [csInf_lt_iff (Uset_bdd H ω) (Uset_ne H ω)]
  constructor
  · rintro ⟨d, ⟨n, k, rfl, hω⟩, hd⟩; exact ⟨n, k, hd, hω⟩
  · rintro ⟨n, k, hd, hω⟩; exact ⟨_, ⟨n, k, rfl, hω⟩, hd⟩

/-- The uniform variable valued in the unit interval. -/
noncomputable def Ui (ω : Ω) : unitInterval :=
  Set.projIcc (0:ℝ) 1 zero_le_one (Uf H ω)

lemma Ui_val (ω : Ω) : (Ui H ω : ℝ) = Uf H ω := by
  unfold Ui
  rw [Set.projIcc_of_mem _ ⟨Uf_nonneg H ω, Uf_le_one H ω⟩]


end defs

section
variable (Q : Measure Ω) [IsProbabilityMeasure Q] (H : Set Ω → Set Ω)
  (hH : ∀ S, MeasurableSet S → H S ⊆ S ∧ MeasurableSet (H S) ∧ Q.real (H S) = Q.real S / 2)
include hH

lemma fam_succ_even (n k : ℕ) : fam H (n + 1) (2 * k) = fam H n k := by
  simp [fam]

lemma fam_succ_odd (n k : ℕ) : fam H (n + 1) (2 * k + 1) =
    fam H n k ∪ H (fam H n (k + 1) \ fam H n k) := by
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [fam, h1, h2]

lemma fam_props (n : ℕ) : (∀ k, MeasurableSet (fam H n k)) ∧ Monotone (fam H n) ∧
    (∀ k, Q.real (fam H n k) = min ((k:ℝ) / 2 ^ n) 1) := by
  induction n with
  | zero =>
    refine ⟨fun k => ?_, ?_, fun k => ?_⟩
    · simp only [fam]; split_ifs <;> simp
    · apply monotone_nat_of_le_succ
      intro k
      simp only [fam]; split_ifs <;> simp_all
    · simp only [fam]
      split_ifs with h
      · subst h; simp
      · have : (1:ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
        simp [min_eq_right this]
  | succ n ih =>
    obtain ⟨hm, hmono, hmeas⟩ := ih
    have hD : ∀ k, MeasurableSet (fam H n (k + 1) \ fam H n k) := fun k => (hm _).diff (hm _)
    have hm' : ∀ j, MeasurableSet (fam H (n + 1) j) := by
      intro j
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
      · rw [fam_succ_even Q H hH]; exact hm k
      · rw [fam_succ_odd Q H hH]; exact (hm k).union (hH _ (hD k)).2.1
    refine ⟨hm', ?_, ?_⟩
    · apply monotone_nat_of_le_succ
      intro j
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
      · rw [fam_succ_even Q H hH, fam_succ_odd Q H hH]; exact Set.subset_union_left
      · rw [fam_succ_odd Q H hH, show 2 * k + 1 + 1 = 2 * (k + 1) by ring, fam_succ_even Q H hH]
        exact Set.union_subset (hmono (Nat.le_succ k))
          ((hH _ (hD k)).1.trans Set.diff_subset)
    · intro j
      obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
      · rw [fam_succ_even Q H hH, hmeas k]
        congr 1
        push_cast
        rw [pow_succ]; field_simp
      · rw [fam_succ_odd Q H hH]
        have hdisj : Disjoint (fam H n k) (H (fam H n (k + 1) \ fam H n k)) :=
          Set.disjoint_left.mpr fun ω h1 h2 => ((hH _ (hD k)).1 h2).2 h1
        rw [measureReal_union hdisj (hH _ (hD k)).2.1, (hH _ (hD k)).2.2,
          measureReal_sdiff (hmono (Nat.le_succ k)) (hm k), hmeas k, hmeas (k + 1)]
        have h2n : (0:ℝ) < 2 ^ n := by positivity
        push_cast
        rcases le_or_gt ((k:ℝ) + 1) (2 ^ n) with hk | hk
        · have e1 : min ((k:ℝ) / 2 ^ n) 1 = k / 2 ^ n :=
            min_eq_left ((div_le_one h2n).mpr (by linarith))
          have e2 : min (((k:ℝ) + 1) / 2 ^ n) 1 = (k + 1) / 2 ^ n :=
            min_eq_left ((div_le_one h2n).mpr hk)
          have e3 : min ((2 * (k:ℝ) + 1) / 2 ^ (n + 1)) 1 = (2 * k + 1) / 2 ^ (n + 1) := by
            apply min_eq_left
            rw [div_le_one (by positivity), pow_succ]; linarith
          rw [e1, e2, e3, pow_succ]; field_simp; ring
        · have hk' : (2:ℝ) ^ n ≤ k := by
            have : (2:ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by push_cast; ring
            rw [this] at hk ⊢
            have : (2 ^ n : ℕ) < k + 1 := by exact_mod_cast hk
            exact_mod_cast Nat.lt_succ_iff.mp this
          have e1 : min ((k:ℝ) / 2 ^ n) 1 = 1 := min_eq_right ((one_le_div h2n).mpr hk')
          have e2 : min (((k:ℝ) + 1) / 2 ^ n) 1 = 1 :=
            min_eq_right ((one_le_div h2n).mpr (by linarith))
          have e3 : min ((2 * (k:ℝ) + 1) / 2 ^ (n + 1)) 1 = 1 := by
            apply min_eq_right
            rw [one_le_div (by positivity), pow_succ]; linarith
          rw [e1, e2, e3]; ring

lemma fam_scale (n m k : ℕ) : fam H (n + m) (k * 2 ^ m) = fam H n k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show n + (m + 1) = (n + m) + 1 by ring, show k * 2 ^ (m + 1) = 2 * (k * 2 ^ m) by ring,
      fam_succ_even Q H hH, ih]

/-- Comparison across levels. -/
lemma fam_le (n k n' k' : ℕ) (h : (k':ℝ) / 2 ^ n' ≤ k / 2 ^ n) : fam H n' k' ⊆ fam H n k := by
  set N := n + n'
  have e1 : fam H n k = fam H N (k * 2 ^ n') := (fam_scale Q H hH n n' k).symm
  have e2 : fam H n' k' = fam H N (k' * 2 ^ n) := by
    rw [show N = n' + n by ring]; exact (fam_scale Q H hH n' n k').symm
  rw [e1, e2]
  apply (fam_props Q H hH N).2.1
  have h1 : (k':ℝ) * 2 ^ n ≤ k * 2 ^ n' := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h; linarith
  exact_mod_cast h1

lemma Uf_measurable : Measurable (Uf H) := by
  apply measurable_of_Iio
  intro a
  have : Uf H ⁻¹' Set.Iio a = ⋃ n : ℕ, ⋃ k : ℕ, {ω | (k:ℝ) / 2 ^ n < a} ∩ fam H n k := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    rw [Uf_lt_iff]
  rw [this]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun k =>
    (MeasurableSet.const _).inter ((fam_props Q H hH n).1 k)

lemma Uf_law_lt (a : ℝ) (ha : 0 < a) : Q.real {ω | Uf H ω < a} = min a 1 := by
  rcases lt_or_ge 1 a with h1 | h1
  · have : {ω | Uf H ω < a} = Set.univ := Set.eq_univ_of_forall fun ω =>
      lt_of_le_of_lt (Uf_le_one H ω) h1
    rw [this, probReal_univ, min_eq_right h1.le]
  rw [min_eq_left h1]
  set K : ℕ → ℕ := fun n => ⌈a * 2 ^ n⌉₊ - 1 with hK
  have hKlt : ∀ n, (K n : ℝ) < a * 2 ^ n := by
    intro n
    have hy : 0 < a * 2 ^ n := by positivity
    have h1 : 1 ≤ ⌈a * 2 ^ n⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
      intro h; rw [Nat.ceil_eq_zero] at h; linarith)
    simp only [hK]
    rw [Nat.cast_sub h1]
    have := Nat.ceil_lt_add_one hy.le
    push_cast; linarith
  have hKmax : ∀ n (k : ℕ), (k:ℝ) < a * 2 ^ n → k ≤ K n := by
    intro n k hk
    have := Nat.lt_ceil.mpr hk
    simp only [hK]; omega
  have hKge : ∀ n, a * 2 ^ n - 1 ≤ (K n : ℝ) := by
    intro n
    have hy : 0 < a * 2 ^ n := by positivity
    have h1 : 1 ≤ ⌈a * 2 ^ n⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
      intro h; rw [Nat.ceil_eq_zero] at h; linarith)
    simp only [hK]
    rw [Nat.cast_sub h1]
    have := Nat.le_ceil (a * 2 ^ n)
    push_cast; linarith
  have hset : {ω | Uf H ω < a} = ⋃ n, fam H n (K n) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [Uf_lt_iff]
    constructor
    · rintro ⟨n, k, hk, hω⟩
      refine ⟨n, (fam_props Q H hH n).2.1 (hKmax n k ?_) hω⟩
      rwa [div_lt_iff₀ (by positivity)] at hk
    · rintro ⟨n, hω⟩
      refine ⟨n, K n, ?_, hω⟩
      rw [div_lt_iff₀ (by positivity)]; exact hKlt n
  have hmono : Monotone (fun n => fam H n (K n)) := by
    apply monotone_nat_of_le_succ
    intro n
    apply fam_le Q H hH
    have h2 : 2 * K n ≤ K (n + 1) := by
      apply hKmax
      push_cast
      have := hKlt n
      rw [pow_succ]; linarith
    have h2' : (2 * K n : ℝ) ≤ K (n + 1) := by exact_mod_cast h2
    rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
    nlinarith [pow_pos (two_pos : (0:ℝ) < 2) n]
  have hmeas : ∀ n, Q.real (fam H n (K n)) = K n / 2 ^ n := by
    intro n
    rw [(fam_props Q H hH n).2.2]
    apply min_eq_left
    rw [div_le_one (by positivity)]
    have := hKlt n; nlinarith [pow_pos (two_pos : (0:ℝ) < 2) n]
  have hlim : Tendsto (fun n => Q.real (fam H n (K n))) atTop (𝓝 (Q.real (⋃ n, fam H n (K n)))) := by
    have := tendsto_measure_iUnion_atTop (μ := Q) hmono
    have := (ENNReal.tendsto_toReal (measure_ne_top Q _)).comp this
    simpa [Function.comp_def, measureReal_def] using this
  rw [hset]
  apply le_antisymm
  · apply le_of_tendsto' hlim
    intro n
    rw [hmeas, div_le_iff₀ (by positivity)]; exact (hKlt n).le
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2:ℝ) < 1)
    have h1 : Q.real (fam H n (K n)) ≤ Q.real (⋃ n, fam H n (K n)) :=
      measureReal_mono (Set.subset_iUnion (fun n => fam H n (K n)) n) (measure_ne_top _ _)
    rw [hmeas] at h1
    have h2 : a - (1/2:ℝ) ^ n ≤ K n / 2 ^ n := by
      rw [le_div_iff₀ (by positivity)]
      have e : (a - (1/2:ℝ)^n) * 2^n = a * 2^n - 1 := by
        rw [sub_mul, one_div_pow, one_div_mul_cancel (by positivity)]
      rw [e]; exact hKge n
    linarith

lemma Uf_law_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Q.real {ω | Uf H ω ≤ x} = x := by
  have hset : {ω | Uf H ω ≤ x} = ⋂ n : ℕ, {ω | Uf H ω < x + 1 / ((n:ℝ) + 1)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h n
      have : 0 < 1 / ((n:ℝ) + 1) := by positivity
      linarith
    · intro h
      by_contra hc
      push Not at hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hc)
      have := h n
      linarith
  have hanti : Antitone (fun n : ℕ => {ω | Uf H ω < x + 1 / ((n:ℝ) + 1)}) := by
    intro n m hnm ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have : 1 / ((m:ℝ) + 1) ≤ 1 / ((n:ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by
        have : (n:ℝ) ≤ m := by exact_mod_cast hnm
        linarith)
    linarith
  have hmeasS : ∀ n : ℕ, MeasurableSet {ω | Uf H ω < x + 1 / ((n:ℝ) + 1)} := fun n =>
    measurableSet_lt (Uf_measurable Q H hH) measurable_const
  have hlim := tendsto_measure_iInter_atTop (μ := Q) (fun n => (hmeasS n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  have hlim' := (ENNReal.tendsto_toReal (measure_ne_top Q _)).comp hlim
  rw [← hset] at hlim'
  have hvals : ∀ n : ℕ, (ENNReal.toReal ∘ (Q ∘ fun n : ℕ => {ω | Uf H ω < x + 1 / ((n:ℝ) + 1)})) n
      = min (x + 1 / ((n:ℝ) + 1)) 1 := by
    intro n
    have : 0 < x + 1 / ((n:ℝ) + 1) := by positivity
    simp only [Function.comp_apply]
    rw [← measureReal_def]; exact Uf_law_lt Q H hH _ this
  have hlim2 : Tendsto (fun n : ℕ => min (x + 1 / ((n:ℝ) + 1)) 1) atTop (𝓝 (min x 1)) := by
    have h : Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h' : Tendsto (fun n : ℕ => x + 1 / ((n:ℝ) + 1)) atTop (𝓝 x) := by
      have := h.const_add x; rwa [add_zero] at this
    exact h'.min tendsto_const_nhds
  have := tendsto_nhds_unique (hlim'.congr hvals) hlim2
  rw [measureReal_def, this, min_eq_left hx1]

lemma Ui_measurable : Measurable (Ui H) :=
  continuous_projIcc.measurable.comp (Uf_measurable Q H hH)

lemma Ui_map : Q.map (Ui H) = volume := by
  have _hq : IsProbabilityMeasure (Q.map (Ui H)) :=
    Measure.isProbabilityMeasure_map (Ui_measurable Q H hH).aemeasurable
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [Measure.map_apply (Ui_measurable Q H hH) measurableSet_Iic, unitInterval.volume_Iic]
  have : Ui H ⁻¹' Set.Iic t = {ω | Uf H ω ≤ t} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    rw [← Subtype.coe_le_coe, Ui_val]
  rw [this, ← ofReal_measureReal (measure_ne_top _ _), Uf_law_le Q H hH t t.2.1 t.2.2]

end

end ESAxUnif

namespace ESAxReal

open ESAxAtomless ESAxUnif

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An atomless probability space supports a uniform random variable. -/
theorem exists_uniform (Q : Measure Ω) [IsProbabilityMeasure Q]
    (hQ : TailRiskSharing.VaRConv.IsAtomless Q) :
    ∃ U : Ω → unitInterval, Measurable U ∧ Q.map U = volume := by
  have hex : ∀ S : Set Ω, ∃ T : Set Ω, MeasurableSet S →
      T ⊆ S ∧ MeasurableSet T ∧ Q.real T = Q.real S / 2 := by
    intro S
    by_cases hS : MeasurableSet S
    · obtain ⟨T, hTS, hT, hPT⟩ := sierpinski Q hQ S hS (Q.real S / 2)
        (by have := (measureReal_nonneg : 0 ≤ Q.real S); linarith)
        (by have := (measureReal_nonneg : 0 ≤ Q.real S); linarith)
      exact ⟨T, fun _ => ⟨hTS, hT, hPT⟩⟩
    · exact ⟨∅, fun h => absurd h hS⟩
  choose H hH using hex
  exact ⟨Ui H, Ui_measurable Q H hH, Ui_map Q H hH⟩

/-- Realization on an event: on an atomless space, for any event `A` of positive probability and
any probability law `ν` on a standard Borel space there is `Z` with `ℙ(A ∩ {Z ∈ S}) = ℙ(A) ν(S)`. -/
theorem exists_realization (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (A : Set Ω) (hA : MeasurableSet A)
    (hApos : P A ≠ 0) {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (ν : Measure Y) [IsProbabilityMeasure ν] :
    ∃ Z : Ω → Y, Measurable Z ∧ ∀ S : Set Y, MeasurableSet S →
      P (A ∩ Z ⁻¹' S) = P A * ν S := by
  have hAtop : P A ≠ ⊤ := measure_ne_top _ _
  set Q : Measure Ω := (P A)⁻¹ • P.restrict A with hQdef
  have hQapp : ∀ s, MeasurableSet s → Q s = (P A)⁻¹ * P (s ∩ A) := by
    intro s hs
    rw [hQdef, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
  have hQprob : IsProbabilityMeasure Q := ⟨by
    rw [hQapp _ MeasurableSet.univ, Set.univ_inter, ENNReal.inv_mul_cancel hApos hAtop]⟩
  have hQat : TailRiskSharing.VaRConv.IsAtomless Q := by
    intro s hs hspos
    rw [hQapp s hs] at hspos
    have h1 : 0 < P (s ∩ A) := by
      rcases eq_or_ne (P (s ∩ A)) 0 with h | h
      · rw [h, mul_zero] at hspos; exact absurd hspos (lt_irrefl 0)
      · exact pos_iff_ne_zero.mpr h
    obtain ⟨t, hts, ht, ht0, htlt⟩ := hP (s ∩ A) (hs.inter hA) h1
    have htA : t ∩ A = t := Set.inter_eq_left.mpr (hts.trans Set.inter_subset_right)
    refine ⟨t, hts.trans Set.inter_subset_left, ht, ?_, ?_⟩
    · rw [hQapp t ht, htA]
      exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hAtop) ht0.ne'
    · rw [hQapp t ht, hQapp s hs, htA]
      exact ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.mpr hAtop)
        (ENNReal.inv_ne_top.mpr hApos) htlt
  obtain ⟨U, hU, hUmap⟩ := exists_uniform Q hQat
  obtain ⟨f, hf, hfmap⟩ := Measure.exists_measurable_map_eq ν
  refine ⟨f ∘ U, hf.comp hU, fun S hS => ?_⟩
  have hmap : Q.map (f ∘ U) = ν := by
    rw [← Measure.map_map hf hU, hUmap, hfmap]
  have h1 : Q ((f ∘ U) ⁻¹' S) = ν S := by
    rw [← Measure.map_apply (hf.comp hU) hS, hmap]
  rw [hQapp _ ((hf.comp hU) hS)] at h1
  rw [← h1, ← mul_assoc, ENNReal.mul_inv_cancel hApos hAtop, one_mul, Set.inter_comm]

end ESAxReal

namespace ESAxP4Aux

open ESAxioms.Characterization ESAxAtomless ESAxReal ESAxA3Aux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma tail_of_threshold (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (A : Set Ω)
    (c : ℝ) (h1 : ∀ᵐ ω ∂P, ω ∈ A → c ≤ X ω) (h2 : ∀ᵐ ω ∂P, ω ∉ A → X ω ≤ c) :
    ∀ᵐ z ∂(P.prod P), z.1 ∈ A → z.2 ∉ A → X z.2 ≤ X z.1 := by
  have k1 := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae h1
  have k2 := (Measure.quasiMeasurePreserving_snd (μ := P) (ν := P)).ae h2
  filter_upwards [k1, k2] with z hz1 hz2 hzA hzA'
  exact le_trans (hz2 hzA') (hz1 hzA)

lemma sameLaw_of_map (P : Measure Ω) (Z W : Ω → ℝ × ℝ) (hZ : Measurable Z) (hW : Measurable W)
    (hmap : P.map Z = P.map W) (g : ℝ × ℝ → ℝ) (hg : Measurable g) :
    SameLaw P (fun ω => g (Z ω)) (fun ω => g (W ω)) := by
  intro x
  have hS : MeasurableSet (g ⁻¹' Set.Iic x) := hg measurableSet_Iic
  have e1 := Measure.map_apply (μ := P) hZ hS
  have e2 := Measure.map_apply (μ := P) hW hS
  rw [hmap] at e1
  simp only [TailRiskSharing.VaRConv.distFn, measureReal_def]
  congr 1
  rw [e1] at e2
  exact e2

lemma memLq_of_map (P : Measure Ω) (q : ENNReal) (Z W : Ω → ℝ × ℝ) (hZ : Measurable Z)
    (hW : Measurable W) (hmap : P.map Z = P.map W) (g : ℝ × ℝ → ℝ) (hg : Measurable g)
    (h : MemLp (fun ω => g (W ω)) q P) : (fun ω => g (Z ω)) ∈ Lq P q := by
  refine ⟨hg.comp hZ, ?_⟩
  have h1 : MemLp g q (P.map W) :=
    (memLp_map_measure_iff hg.aestronglyMeasurable hW.aemeasurable).mpr h
  rw [← hmap] at h1
  exact (memLp_map_measure_iff hg.aestronglyMeasurable hZ.aemeasurable).mp h1

theorem part2 (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (q : ENNReal) (ρ : (Ω → ℝ) → ℝ)
    (hLI : AxiomLI P (Lq P q) ρ) (A : Set Ω) (hA : IsStressEvent P (Lq P q) ρ A) :
    IsPAdditive P (1 - P.real A) (Lq P q) ρ := by
  obtain ⟨hAm, hA0, hA1, hNRC⟩ := hA
  set p := 1 - P.real A with hpdef
  have hp : p ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  intro X hX Y hY ⟨B, hB⟩
  have hBX : IsPTailEvent P p X B := hB 0
  have hBY : IsPTailEvent P p Y B := hB 1
  have hBm : MeasurableSet B := hBX.1.1
  have hPB : P.real B = 1 - p := hBX.2
  -- thresholds
  obtain ⟨-, hX1, hX2⟩ := ((lemmaA3 P hP p hp X hX.1).1 B hBm).mp hBX
  obtain ⟨-, hY1, hY2⟩ := ((lemmaA3 P hP p hp Y hY.1).1 B hBm).mp hBY
  set cX := VaR P p X
  set cY := VaR P p Y
  -- measures of A, B
  have hPAB : P A = P B := by
    rw [← ofReal_measureReal (μ := P) (s := A), ← ofReal_measureReal (μ := P) (s := B), hPB]
    simp only [hpdef, sub_sub_cancel]
  have hPAcBc : P Aᶜ = P Bᶜ := by
    rw [prob_compl_eq_one_sub hAm, prob_compl_eq_one_sub hBm, hPAB]
  have hPB0 : P B ≠ 0 := by
    intro h; rw [measureReal_def, h] at hPB; simp at hPB; linarith [hp.2]
  have hPBc0 : P Bᶜ ≠ 0 := by
    intro h
    have : P.real Bᶜ = 0 := by rw [measureReal_def, h]; simp
    rw [probReal_compl_eq_one_sub hBm, hPB] at this; linarith [hp.1]
  have hPA0 : P A ≠ 0 := by rw [hPAB]; exact hPB0
  have hPAc0 : P Aᶜ ≠ 0 := by rw [hPAcBc]; exact hPBc0
  -- the pair and its conditional laws
  set W : Ω → ℝ × ℝ := fun ω => (X ω, Y ω) with hWdef
  have hW : Measurable W := hX.1.prodMk hY.1
  set ν1 : Measure (ℝ × ℝ) := (P B)⁻¹ • (P.restrict B).map W
  set ν2 : Measure (ℝ × ℝ) := (P Bᶜ)⁻¹ • (P.restrict Bᶜ).map W
  have hν1 : ∀ S, MeasurableSet S → ν1 S = (P B)⁻¹ * P (W ⁻¹' S ∩ B) := by
    intro S hS
    simp only [ν1, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply hW hS, Measure.restrict_apply (hW hS)]
  have hν2 : ∀ S, MeasurableSet S → ν2 S = (P Bᶜ)⁻¹ * P (W ⁻¹' S ∩ Bᶜ) := by
    intro S hS
    simp only [ν2, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply hW hS, Measure.restrict_apply (hW hS)]
  have hν1p : IsProbabilityMeasure ν1 := ⟨by
    rw [hν1 _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter,
      ENNReal.inv_mul_cancel hPB0 (measure_ne_top _ _)]⟩
  have hν2p : IsProbabilityMeasure ν2 := ⟨by
    rw [hν2 _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter,
      ENNReal.inv_mul_cancel hPBc0 (measure_ne_top _ _)]⟩
  obtain ⟨Z1, hZ1, hZ1law⟩ := exists_realization P hP A hAm hPA0 ν1
  obtain ⟨Z2, hZ2, hZ2law⟩ := exists_realization P hP Aᶜ hAm.compl hPAc0 ν2
  classical
  set Z : Ω → ℝ × ℝ := A.piecewise Z1 Z2 with hZdef
  have hZ : Measurable Z := Measurable.piecewise hAm hZ1 hZ2
  have keyA : ∀ S, MeasurableSet S → P (A ∩ Z ⁻¹' S) = P (B ∩ W ⁻¹' S) := by
    intro S hS
    have : A ∩ Z ⁻¹' S = A ∩ Z1 ⁻¹' S := by
      ext ω; simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hZdef, Set.piecewise_eq_of_mem _ _ _ h1] at h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hZdef, Set.piecewise_eq_of_mem _ _ _ h1]⟩
    rw [this, hZ1law S hS, hν1 S hS, hPAB, ← mul_assoc,
      ENNReal.mul_inv_cancel hPB0 (measure_ne_top _ _), one_mul, Set.inter_comm]
  have keyAc : ∀ S, MeasurableSet S → P (Aᶜ ∩ Z ⁻¹' S) = P (Bᶜ ∩ W ⁻¹' S) := by
    intro S hS
    have : Aᶜ ∩ Z ⁻¹' S = Aᶜ ∩ Z2 ⁻¹' S := by
      ext ω; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hZdef, Set.piecewise_eq_of_notMem _ _ _ h1] at h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hZdef, Set.piecewise_eq_of_notMem _ _ _ h1]⟩
    rw [this, hZ2law S hS, hν2 S hS, hPAcBc, ← mul_assoc,
      ENNReal.mul_inv_cancel hPBc0 (measure_ne_top _ _), one_mul, Set.inter_comm]
  have hmap : P.map Z = P.map W := by
    ext S hS
    rw [Measure.map_apply hZ hS, Measure.map_apply hW hS,
      ← measure_inter_add_sdiff (Z ⁻¹' S) hAm, ← measure_inter_add_sdiff (W ⁻¹' S) hBm]
    have f1 : Z ⁻¹' S ∩ A = A ∩ Z ⁻¹' S := Set.inter_comm _ _
    have f2 : Z ⁻¹' S \ A = Aᶜ ∩ Z ⁻¹' S := by rw [Set.sdiff_eq, Set.inter_comm]
    have f3 : W ⁻¹' S ∩ B = B ∩ W ⁻¹' S := Set.inter_comm _ _
    have f4 : W ⁻¹' S \ B = Bᶜ ∩ W ⁻¹' S := by rw [Set.sdiff_eq, Set.inter_comm]
    rw [f1, f2, f3, f4, keyA S hS, keyAc S hS]
  -- the new pair
  set X' : Ω → ℝ := fun ω => (Z ω).1
  set Y' : Ω → ℝ := fun ω => (Z ω).2
  have hX' : X' ∈ Lq P q := memLq_of_map P q Z W hZ hW hmap Prod.fst measurable_fst hX.2
  have hY' : Y' ∈ Lq P q := memLq_of_map P q Z W hZ hW hmap Prod.snd measurable_snd hY.2
  have hXY : X + Y ∈ Lq P q := ⟨hX.1.add hY.1, hX.2.add hY.2⟩
  have hXY' : X' + Y' ∈ Lq P q := ⟨hX'.1.add hY'.1, hX'.2.add hY'.2⟩
  have hsX : SameLaw P X' X := sameLaw_of_map P Z W hZ hW hmap Prod.fst measurable_fst
  have hsY : SameLaw P Y' Y := sameLaw_of_map P Z W hZ hW hmap Prod.snd measurable_snd
  have hsXY : SameLaw P (X' + Y') (X + Y) :=
    sameLaw_of_map P Z W hZ hW hmap (fun z => z.1 + z.2) (measurable_fst.add measurable_snd)
  -- tail events transfer
  have transfer : ∀ (g : ℝ × ℝ → ℝ), Measurable g → ∀ c : ℝ,
      (∀ᵐ ω ∂P, ω ∈ B → c ≤ g (W ω)) → (∀ᵐ ω ∂P, ω ∉ B → g (W ω) ≤ c) →
      IsTailEvent P (fun ω => g (Z ω)) A := by
    intro g hg c h1 h2
    refine ⟨hAm, hA0, hA1, tail_of_threshold P (fun ω => g (Z ω)) A c ?_ ?_⟩
    · rw [ae_iff] at h1 ⊢
      have hS : MeasurableSet {z : ℝ × ℝ | g z < c} := measurableSet_lt hg measurable_const
      have e1 : {ω | ¬(ω ∈ A → c ≤ g (Z ω))} = A ∩ Z ⁻¹' {z | g z < c} := by
        ext ω; simp
      have e2 : {ω | ¬(ω ∈ B → c ≤ g (W ω))} = B ∩ W ⁻¹' {z | g z < c} := by
        ext ω; simp
      rw [e1, keyA _ hS, ← e2, h1]
    · rw [ae_iff] at h2 ⊢
      have hS : MeasurableSet {z : ℝ × ℝ | c < g z} := measurableSet_lt measurable_const hg
      have e1 : {ω | ¬(ω ∉ A → g (Z ω) ≤ c)} = Aᶜ ∩ Z ⁻¹' {z | c < g z} := by
        ext ω; simp
      have e2 : {ω | ¬(ω ∉ B → g (W ω) ≤ c)} = Bᶜ ∩ W ⁻¹' {z | c < g z} := by
        ext ω; simp
      rw [e1, keyAc _ hS, ← e2, h2]
  have thr1 : ∀ (V : Ω → ℝ) (c : ℝ), {ω | c < V ω} ≤ᵐ[P] B → (∀ᵐ ω ∂P, ω ∉ B → V ω ≤ c) := by
    intro V c h
    filter_upwards [h] with ω hω hωB
    by_contra hc
    push Not at hc
    exact hωB (hω hc)
  have htX : IsTailEvent P X' A := transfer Prod.fst measurable_fst cX hX2 (thr1 X cX hX1)
  have htY : IsTailEvent P Y' A := transfer Prod.snd measurable_snd cY hY2 (thr1 Y cY hY1)
  have hadd := hNRC X' hX' Y' hY' htX htY
  rw [hLI X hX X' hX' (fun x => (hsX x).symm), hLI Y hY Y' hY' (fun x => (hsY x).symm),
    hLI (X + Y) hXY (X' + Y') hXY' (fun x => (hsXY x).symm)]
  exact hadd

theorem prop4 (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (q : ENNReal)
    (ρ : (Ω → ℝ) → ℝ) (hLI : AxiomLI P (Lq P q) ρ) :
    (AxiomNRC P (Lq P q) ρ ↔ ∃ p ∈ Set.Ioo (0 : ℝ) 1, IsPAdditive P p (Lq P q) ρ) ∧
    ∀ A : Set Ω, IsStressEvent P (Lq P q) ρ A → IsPAdditive P (1 - P.real A) (Lq P q) ρ := by
  refine ⟨⟨fun ⟨A, hA⟩ => ⟨1 - P.real A, ⟨by linarith [hA.2.2.1], by linarith [hA.2.1]⟩,
    part2 P hP q ρ hLI A hA⟩, fun ⟨p, hp, hadd⟩ => ?_⟩, part2 P hP q ρ hLI⟩
  obtain ⟨A, -, hAm, hPA⟩ := sierpinski P hP Set.univ MeasurableSet.univ (1 - p)
    (by linarith [hp.2]) (by rw [probReal_univ]; linarith [hp.1])
  refine ⟨A, hAm, by linarith [hp.2], by linarith [hp.1], fun X hX Y hY htX htY => ?_⟩
  apply hadd X hX Y hY
  refine ⟨A, fun i => ?_⟩
  fin_cases i
  · exact ⟨htX, hPA⟩
  · exact ⟨htY, hPA⟩

end ESAxP4Aux


namespace ESAxESF

open ESAxioms.Characterization ESAxP1Aux ESAxA3Aux

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `(1-p) ESₚ(X) = (1-p) xₚ + 𝔼[(X - xₚ)⁺]`. -/
lemma ES_formula (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (X : Ω → ℝ) (hX : X ∈ L1 P) :
    (1 - p) * ES P p X = (1 - p) * VaR P p X + ∫ ω, max (X ω - VaR P p X) 0 ∂P := by
  set x := VaR P p X with hx
  have hp1 : (1 - p) ≠ 0 := by linarith [hp.2]
  unfold ES
  rw [← mul_assoc, mul_inv_cancel₀ hp1, one_mul]
  have hint := VaR_integrableOn' P X hX p hp
  -- split off the constant
  have h1 : ∫ q in Set.Ioo p 1, VaR P q X = (∫ q in Set.Ioo p 1, (VaR P q X - x)) + (1 - p) * x := by
    rw [integral_sub hint (integrable_const x), setIntegral_const, Real.volume_real_Ioo_of_le hp.2.le,
      smul_eq_mul]
    ring
  have h2 : ∫ q in Set.Ioo p 1, (VaR P q X - x) = ∫ q in Set.Ioo p 1, max (VaR P q X - x) 0 := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro q hq
    have : x ≤ VaR P q X := VaR_mono_q P X hX.1 hp ⟨lt_trans hp.1 hq.1, hq.2⟩ hq.1.le
    simp only
    rw [max_eq_left (by linarith)]
  have h3 : ∫ q in Set.Ioo 0 1, max (VaR P q X - x) 0 = ∫ q in Set.Ioo p 1, max (VaR P q X - x) 0 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (Set.Ioo_subset_Ioo_left hp.1.le)
    intro q hq
    have hq1 : q ∈ Set.Ioo (0:ℝ) 1 := hq.1
    have hqp : q ≤ p := by
      by_contra h; push Not at h; exact hq.2 ⟨h, hq1.2⟩
    have : VaR P q X ≤ x := VaR_mono_q P X hX.1 hq1 hp hqp
    exact max_eq_right (by linarith)
  have h4 : ∫ q in Set.Ioo 0 1, max (VaR P q X - x) 0 = ∫ ω, max (X ω - x) 0 ∂P := by
    have hQ := VaR_aemeas P X hX.1 0 1 le_rfl le_rfl
    have hg : Continuous (fun y : ℝ => max (y - x) 0) := by fun_prop
    have e1 : ∫ y, max (y - x) 0 ∂((volume.restrict (Set.Ioo (0:ℝ) 1)).map (fun q => VaR P q X)) =
        ∫ q in Set.Ioo 0 1, max (VaR P q X - x) 0 :=
      integral_map hQ hg.aestronglyMeasurable
    have e2 : ∫ y, max (y - x) 0 ∂(P.map X) = ∫ ω, max (X ω - x) 0 ∂P :=
      integral_map hX.1.aemeasurable hg.aestronglyMeasurable
    rw [← e1, map_VaR P X hX.1, e2]
  rw [h1, h2, ← h3, h4]; ring

/-- For a `p`-tail event `B` of `X`, `𝔼[(X - xₚ)⁺] = 𝔼[(X - xₚ) 1_B]`. -/
lemma pos_part_eq (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (X : Ω → ℝ) (hX : X ∈ L1 P) (B : Set Ω) (hB : IsPTailEvent P p X B) :
    (fun ω => max (X ω - VaR P p X) 0) =ᵐ[P] B.indicator (fun ω => X ω - VaR P p X) := by
  obtain ⟨-, h1, h2⟩ := ((lemmaA3 P hP p hp X hX.1).1 B hB.1.1).mp hB
  filter_upwards [h1, h2] with ω hω1 hω2
  by_cases hωB : ω ∈ B
  · rw [Set.indicator_of_mem hωB]
    have : VaR P p X ≤ X ω := hω2 hωB
    exact max_eq_left (by linarith)
  · rw [Set.indicator_of_notMem hωB]
    have : X ω ≤ VaR P p X := by
      by_contra h; push Not at h; exact hωB (hω1 h)
    exact max_eq_right (by linarith)

/-- Lemma A.7 (⇐): `ESₚ(X) = 𝔼[X 1_B] / (1 - p)` for a `p`-tail event `B`. -/
lemma ES_tail (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (X : Ω → ℝ) (hX : X ∈ L1 P) (B : Set Ω) (hB : IsPTailEvent P p X B) :
    (1 - p) * ES P p X = ∫ ω in B, X ω ∂P := by
  rw [ES_formula P p hp X hX, integral_congr_ae (pos_part_eq P hP p hp X hX B hB),
    integral_indicator hB.1.1, integral_sub hX.2.integrableOn (integrable_const _),
    setIntegral_const, hB.2, smul_eq_mul]
  ring

lemma tail_add (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (X Y : Ω → ℝ) (B : Set Ω)
    (hX : IsPTailEvent P p X B) (hY : IsPTailEvent P p Y B) : IsPTailEvent P p (X + Y) B := by
  refine ⟨⟨hX.1.1, hX.1.2.1, hX.1.2.2.1, ?_⟩, hX.2⟩
  filter_upwards [hX.1.2.2.2, hY.1.2.2.2] with z h1 h2 hz1 hz2
  simp only [Pi.add_apply]
  linarith [h1 hz1 hz2, h2 hz1 hz2]

/-- `ESₚ` is `p`-additive on `L¹`. -/
lemma ES_padd (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) :
    IsPAdditive P p (L1 P) (ES P p) := by
  intro X hX Y hY ⟨B, hB⟩
  have hBX : IsPTailEvent P p X B := hB 0
  have hBY : IsPTailEvent P p Y B := hB 1
  have hXY : X + Y ∈ L1 P := ⟨hX.1.add hY.1, hX.2.add hY.2⟩
  have h1 := ES_tail P hP p hp X hX B hBX
  have h2 := ES_tail P hP p hp Y hY B hBY
  have h3 := ES_tail P hP p hp (X + Y) hXY B (tail_add P p X Y B hBX hBY)
  simp only [Pi.add_apply] at h3
  rw [integral_add hX.2.integrableOn hY.2.integrableOn] at h3
  have hp1 : (1 - p) ≠ 0 := by linarith [hp.2]
  apply mul_left_cancel₀ hp1
  rw [mul_add, h1, h2, h3]

end ESAxESF

namespace ESAxA1Aux

open ESAxioms.Characterization ESAxAtomless

variable {Ω : Type*} [MeasurableSpace Ω]

lemma sameLaw_of_ae (P : Measure Ω) {X Y : Ω → ℝ} (h : X =ᵐ[P] Y) : SameLaw P X Y := by
  intro x
  apply measureReal_congr
  filter_upwards [h] with ω hω
  show (X ω ≤ x) = (Y ω ≤ x)
  rw [hω]

/-- `𝟙_B`. -/
noncomputable def I (B : Set Ω) : Ω → ℝ := B.indicator (fun _ => (1:ℝ))

lemma I_nonneg (B : Set Ω) (ω : Ω) : 0 ≤ I B ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω

lemma I_le_one (B : Set Ω) (ω : Ω) : I B ω ≤ 1 := by
  unfold I; by_cases h : ω ∈ B <;> simp [h]

lemma I_mem (P : Measure Ω) [IsProbabilityMeasure P] (B : Set Ω) (hB : MeasurableSet B) :
    I B ∈ L1Plus P :=
  ⟨⟨measurable_const.indicator hB, (integrable_const (1:ℝ)).indicator hB⟩, I_nonneg B⟩

lemma distFn_I (P : Measure Ω) [IsProbabilityMeasure P] (B : Set Ω) (hB : MeasurableSet B)
    (x : ℝ) : TailRiskSharing.VaRConv.distFn P (I B) x =
      if x < 0 then 0 else if x < 1 then 1 - P.real B else 1 := by
  unfold TailRiskSharing.VaRConv.distFn
  split_ifs with h1 h2
  · have : {ω | I B ω ≤ x} = ∅ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le h1 (I_nonneg B ω)
    rw [this]; simp
  · have : {ω | I B ω ≤ x} = Bᶜ := by
      ext ω; unfold I; by_cases h : ω ∈ B <;> simp [h] <;> push Not at h1 <;> linarith
    rw [this, probReal_compl_eq_one_sub hB]
  · have : {ω | I B ω ≤ x} = Set.univ := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      push Not at h2; exact le_trans (I_le_one B ω) h2
    rw [this, probReal_univ]

lemma sameLaw_I (P : Measure Ω) [IsProbabilityMeasure P] (B C : Set Ω) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (h : P.real B = P.real C) : SameLaw P (I B) (I C) := by
  intro x; rw [distFn_I P B hB, distFn_I P C hC, h]

lemma smul_mem (P : Measure Ω) {X : Ω → ℝ} (hX : X ∈ L1Plus P) (c : ℝ) (hc : 0 ≤ c) :
    c • X ∈ L1Plus P :=
  ⟨⟨hX.1.1.const_smul c, hX.1.2.smul c⟩, fun ω => mul_nonneg hc (hX.2 ω)⟩

lemma add_mem (P : Measure Ω) {X Y : Ω → ℝ} (hX : X ∈ L1Plus P) (hY : Y ∈ L1Plus P) :
    X + Y ∈ L1Plus P :=
  ⟨⟨hX.1.1.add hY.1.1, hX.1.2.add hY.1.2⟩, fun ω => add_nonneg (hX.2 ω) (hY.2 ω)⟩

lemma zero_mem (P : Measure Ω) : (0 : Ω → ℝ) ∈ L1Plus P :=
  ⟨⟨measurable_const, integrable_zero _ _ _⟩, fun _ => le_rfl⟩

section
variable (P : Measure Ω) [IsProbabilityMeasure P] (ρ : (Ω → ℝ) → ℝ)
  (hM : AxiomM (L1Plus P) ρ) (hA : IsAdditiveOn (L1Plus P) ρ)

include hA in
lemma rho_zero : ρ 0 = 0 := by
  have := hA 0 (zero_mem P) 0 (zero_mem P)
  rw [add_zero] at this; linarith

include hM hA in
lemma rho_nonneg {X : Ω → ℝ} (hX : X ∈ L1Plus P) : 0 ≤ ρ X := by
  have := hM 0 (zero_mem P) X hX hX.2
  rwa [rho_zero P ρ hA] at this

include hA in
lemma rho_nat {X : Ω → ℝ} (hX : X ∈ L1Plus P) (n : ℕ) : ρ ((n:ℝ) • X) = n * ρ X := by
  induction n with
  | zero => simp [rho_zero P ρ hA]
  | succ n ih =>
    have e : ((n + 1 : ℕ) : ℝ) • X = (n:ℝ) • X + X := by
      push_cast; rw [add_smul, one_smul]
    rw [e, hA _ (smul_mem P hX _ (Nat.cast_nonneg n)) _ hX, ih]; push_cast; ring

include hA in
lemma rho_natdiv {X : Ω → ℝ} (hX : X ∈ L1Plus P) (k n : ℕ) (hn : 0 < n) :
    ρ (((k:ℝ) / n) • X) = (k / n) * ρ X := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : ρ X = n * ρ ((1 / (n:ℝ)) • X) := by
    rw [← rho_nat P ρ hA (smul_mem P hX _ (by positivity)) n, smul_smul, mul_one_div_cancel hn',
      one_smul]
  have h2 : ((k:ℝ) / n) • X = (k:ℝ) • ((1 / (n:ℝ)) • X) := by
    rw [smul_smul]; congr 1; ring
  rw [h2, rho_nat P ρ hA (smul_mem P hX _ (by positivity)) k, h1]
  field_simp

include hM hA in
lemma rho_smul {X : Ω → ℝ} (hX : X ∈ L1Plus P) (c : ℝ) (hc : 0 ≤ c) :
    ρ (c • X) = c * ρ X := by
  have hρX := rho_nonneg P ρ hM hA hX
  have mono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → ρ (a • X) ≤ ρ (b • X) := by
    intro a b ha hab
    apply hM _ (smul_mem P hX a ha) _ (smul_mem P hX b (le_trans ha hab))
    intro ω; simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_le_mul_of_nonneg_right hab (hX.2 ω)
  have key : ∀ n : ℕ, 0 < n → |ρ (c • X) - c * ρ X| ≤ ρ X / n := by
    intro n hn
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    set k := ⌊c * n⌋₊ with hk
    have hk1 : (k:ℝ) ≤ c * n := Nat.floor_le (by positivity)
    have hk2 : c * n < k + 1 := Nat.lt_floor_add_one _
    have lo : ρ (((k:ℝ) / n) • X) ≤ ρ (c • X) :=
      mono _ _ (by positivity) (by rw [div_le_iff₀ hn']; linarith)
    have hi : ρ (c • X) ≤ ρ ((((k + 1 : ℕ) : ℝ) / n) • X) :=
      mono _ _ hc (by rw [le_div_iff₀ hn']; push_cast; linarith)
    rw [rho_natdiv P ρ hA hX k n hn] at lo
    rw [rho_natdiv P ρ hA hX (k + 1) n hn] at hi
    push_cast at hi
    rw [abs_le]
    have e1 : (k:ℝ) / n ≥ c - 1 / n := by
      rw [ge_iff_le, show c - 1 / (n:ℝ) = (c * n - 1) / n by field_simp]
      exact div_le_div_of_nonneg_right (by linarith) hn'.le
    have e2 : ((k:ℝ) + 1) / n ≤ c + 1 / n := by
      rw [show c + 1 / (n:ℝ) = (c * n + 1) / n by field_simp]
      exact div_le_div_of_nonneg_right (by linarith) hn'.le
    constructor
    · have : (c - 1 / n) * ρ X ≤ (k / n) * ρ X := mul_le_mul_of_nonneg_right e1 hρX
      have : ρ X / n = 1 / n * ρ X := by ring
      nlinarith
    · have : ((k + 1) / n) * ρ X ≤ (c + 1 / n) * ρ X := mul_le_mul_of_nonneg_right e2 hρX
      have : ρ X / n = 1 / n * ρ X := by ring
      nlinarith
  apply eq_of_abs_sub_nonpos
  by_contra hpos
  push Not at hpos
  obtain ⟨n, hn⟩ := exists_nat_gt (ρ X / |ρ (c • X) - c * ρ X|)
  have hn0 : 0 < n := by
    have : 0 ≤ ρ X / |ρ (c • X) - c * ρ X| := div_nonneg hρX (abs_nonneg _)
    exact_mod_cast lt_of_le_of_lt this hn
  have := key n hn0
  have hn' : (0:ℝ) < n := by exact_mod_cast hn0
  rw [div_lt_iff₀ hpos] at hn
  rw [le_div_iff₀ hn'] at this
  linarith

end

end ESAxA1Aux

namespace ESAxA1Aux

open ESAxioms.Characterization ESAxAtomless

variable {Ω : Type*} [MeasurableSpace Ω]

lemma I_union (B C : Set Ω) (h : Disjoint B C) : I (B ∪ C) = I B + I C := by
  unfold I; ext ω; simp [Set.indicator_union_of_disjoint h]

lemma I_mono {B C : Set Ω} (h : B ⊆ C) (ω : Ω) : I B ω ≤ I C ω := by
  unfold I
  exact Set.indicator_le_indicator_of_subset h (fun _ => zero_le_one) ω

lemma real_le_one (P : Measure Ω) [IsProbabilityMeasure P] (B : Set Ω) : P.real B ≤ 1 := by
  have := measureReal_mono (μ := P) (Set.subset_univ B) (measure_ne_top _ _)
  rwa [probReal_univ] at this

section
variable (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
  (ρ : (Ω → ℝ) → ℝ)
  (hM : AxiomM (L1Plus P) ρ) (hA : IsAdditiveOn (L1Plus P) ρ) (hLI : AxiomLI P (L1Plus P) ρ)

include hLI in
lemma rho_I_eq (B C : Set Ω) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (h : P.real B = P.real C) : ρ (I B) = ρ (I C) :=
  hLI _ (I_mem P B hB) _ (I_mem P C hC) (sameLaw_I P B C hB hC h)

include hP hM hA hLI in
lemma rho_I (B : Set Ω) (hB : MeasurableSet B) : ρ (I B) = ρ (I Set.univ) * P.real B := by
  set lam := ρ (I Set.univ) with hlam
  have hex : ∀ t : ℝ, 0 ≤ t ∧ t ≤ 1 → ∃ B : Set Ω, MeasurableSet B ∧ P.real B = t := by
    intro t ht
    obtain ⟨T, -, hT, hPT⟩ := sierpinski P hP Set.univ MeasurableSet.univ t ht.1
      (by rw [probReal_univ]; exact ht.2)
    exact ⟨T, hT, hPT⟩
  classical
  let T : ℝ → Set Ω := fun t => if h : 0 ≤ t ∧ t ≤ 1 then Classical.choose (hex t h) else ∅
  have hT : ∀ t, 0 ≤ t → t ≤ 1 → MeasurableSet (T t) ∧ P.real (T t) = t := by
    intro t h0 h1
    have h : 0 ≤ t ∧ t ≤ 1 := ⟨h0, h1⟩
    simp only [T, dif_pos h]
    exact Classical.choose_spec (hex t h)
  let g : ℝ → ℝ := fun t => ρ (I (T t))
  have g_spec : ∀ B, MeasurableSet B → ρ (I B) = g (P.real B) := by
    intro B hB
    have h := hT (P.real B) measureReal_nonneg (real_le_one P B)
    exact rho_I_eq P ρ hLI B _ hB h.1 h.2.symm
  have g_add : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ 1 → g (s + t) = g s + g t := by
    intro s t hs ht hst
    obtain ⟨hBm, hPB⟩ := hT s hs (by linarith)
    obtain ⟨C, hCB, hCm, hPC⟩ := sierpinski P hP (T s)ᶜ hBm.compl t ht
      (by rw [probReal_compl_eq_one_sub hBm, hPB]; linarith)
    have hdisj : Disjoint (T s) C := Set.disjoint_left.mpr fun ω h1 h2 => hCB h2 h1
    have hU : P.real (T s ∪ C) = s + t := by rw [measureReal_union hdisj hCm, hPB, hPC]
    rw [← hU, ← g_spec _ (hBm.union hCm), I_union _ _ hdisj,
      hA _ (I_mem P _ hBm) _ (I_mem P _ hCm), g_spec _ hBm, g_spec _ hCm, hPB, hPC]
  have g_mono : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → g s ≤ g t := by
    intro s t hs hst ht
    obtain ⟨hCm, hPC⟩ := hT t (le_trans hs hst) ht
    obtain ⟨B, hBC, hBm, hPB⟩ := sierpinski P hP (T t) hCm s hs (by rw [hPC]; exact hst)
    rw [← hPB, ← g_spec _ hBm]
    exact hM _ (I_mem P _ hBm) _ (I_mem P _ hCm) (I_mono hBC)
  have g_one : g 1 = lam := by
    rw [hlam, g_spec _ MeasurableSet.univ, probReal_univ]
  have g_zero : g 0 = 0 := by
    have := g_add 0 0 le_rfl le_rfl (by norm_num)
    simp only [add_zero] at this; linarith
  have g_nat : ∀ k : ℕ, ∀ s, 0 ≤ s → (k:ℝ) * s ≤ 1 → g (k * s) = k * g s := by
    intro k
    induction k with
    | zero => intro s _ _; simp [g_zero]
    | succ k ih =>
      intro s hs hks
      push_cast at hks ⊢
      have h1 : (k:ℝ) * s ≤ 1 := by nlinarith
      rw [add_mul, one_mul, g_add _ _ (by positivity) hs (by linarith), ih s hs h1]; ring
  have lam_nonneg : 0 ≤ lam := rho_nonneg P ρ hM hA (I_mem P _ MeasurableSet.univ)
  have g_frac : ∀ n k : ℕ, 0 < n → k ≤ n → g ((k:ℝ) / n) = k / n * lam := by
    intro n k hn hkn
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    have h1 : g 1 = n * g (1 / n) := by
      rw [← g_nat n (1 / n) (by positivity) (by rw [mul_one_div_cancel hn'.ne'])]
      rw [mul_one_div_cancel hn'.ne']
    have hk : (k:ℝ) ≤ n := by exact_mod_cast hkn
    have h2 : g ((k:ℝ) / n) = k * g (1 / n) := by
      rw [← g_nat k (1 / n) (by positivity) (by rw [mul_one_div, div_le_one hn']; exact hk)]
      rw [mul_one_div]
    rw [h2, g_one] at *
    rw [h1]; field_simp
  have g_lin : ∀ t, 0 ≤ t → t ≤ 1 → g t = lam * t := by
    intro t h0 h1
    rcases eq_or_lt_of_le h1 with heq | hlt
    · rw [heq, g_one, mul_one]
    have key : ∀ n : ℕ, 0 < n → |g t - lam * t| ≤ lam / n := by
      intro n hn
      have hn' : (0:ℝ) < n := by exact_mod_cast hn
      set k := ⌊t * n⌋₊ with hk
      have hk1 : (k:ℝ) ≤ t * n := Nat.floor_le (by positivity)
      have hk2 : t * n < k + 1 := Nat.lt_floor_add_one _
      have hkn : k + 1 ≤ n := by
        have : (k:ℝ) < n := by nlinarith
        exact_mod_cast this
      have lo := g_mono ((k:ℝ) / n) t (by positivity) (by rw [div_le_iff₀ hn']; linarith) h1
      have hi := g_mono t (((k + 1 : ℕ):ℝ) / n) h0
        (by rw [le_div_iff₀ hn']; push_cast; linarith)
        (by rw [div_le_one hn']; exact_mod_cast hkn)
      rw [g_frac n k hn (by omega)] at lo
      rw [g_frac n (k + 1) hn hkn] at hi
      push_cast at hi
      have e1 : (k:ℝ) / n ≥ t - 1 / n := by
        rw [ge_iff_le, show t - 1 / (n:ℝ) = (t * n - 1) / n by field_simp]
        exact div_le_div_of_nonneg_right (by linarith) hn'.le
      have e2 : ((k:ℝ) + 1) / n ≤ t + 1 / n := by
        rw [show t + 1 / (n:ℝ) = (t * n + 1) / n by field_simp]
        exact div_le_div_of_nonneg_right (by linarith) hn'.le
      rw [abs_le]
      have hl : lam / n = 1 / n * lam := by ring
      constructor
      · have := mul_le_mul_of_nonneg_right e1 lam_nonneg
        nlinarith
      · have := mul_le_mul_of_nonneg_right e2 lam_nonneg
        nlinarith
    apply eq_of_abs_sub_nonpos
    by_contra hpos
    push Not at hpos
    obtain ⟨n, hn⟩ := exists_nat_gt (lam / |g t - lam * t|)
    have hn0 : 0 < n := by
      have : 0 ≤ lam / |g t - lam * t| := div_nonneg lam_nonneg (abs_nonneg _)
      exact_mod_cast lt_of_le_of_lt this hn
    have := key n hn0
    have hn' : (0:ℝ) < n := by exact_mod_cast hn0
    rw [div_lt_iff₀ hpos] at hn
    rw [le_div_iff₀ hn'] at this
    linarith
  rw [g_spec B hB, g_lin _ measureReal_nonneg (real_le_one P B)]

end

end ESAxA1Aux

namespace ESAxA1Aux

open ESAxioms.Characterization ESAxAtomless

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integral_I (P : Measure Ω) [IsProbabilityMeasure P] (B : Set Ω) (hB : MeasurableSet B) :
    ∫ ω, I B ω ∂P = P.real B := by
  unfold I; rw [integral_indicator_const _ hB]; simp

lemma sum_mem (P : Measure Ω) {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, f i ∈ L1Plus P) : (∑ i ∈ s, f i) ∈ L1Plus P := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem P
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact add_mem P (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma rho_sum (P : Measure Ω) [IsProbabilityMeasure P] (ρ : (Ω → ℝ) → ℝ) (hA : IsAdditiveOn (L1Plus P) ρ)
    {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, f i ∈ L1Plus P) : ρ (∑ i ∈ s, f i) = ∑ i ∈ s, ρ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rho_zero P ρ hA
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [hA _ (hf a (Finset.mem_insert_self a s)) _
      (sum_mem P s f fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    rw [ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

/-- Counting lemma for the layer sums. -/
lemma card_filter_le (N : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hyN : y ≤ N) :
    ((Finset.range N).filter (fun k : ℕ => ((k:ℝ) + 1) ≤ y)).card = ⌊y⌋₊ := by
  have : (Finset.range N).filter (fun k : ℕ => ((k:ℝ) + 1) ≤ y) = Finset.range ⌊y⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    have hfl : ⌊y⌋₊ ≤ N := Nat.floor_le_of_le hyN
    constructor
    · rintro ⟨_, hk⟩
      have : k + 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hk)
      omega
    · intro hk
      refine ⟨by omega, ?_⟩
      have : k + 1 ≤ ⌊y⌋₊ := hk
      have h2 : ((k + 1 : ℕ) : ℝ) ≤ y := (Nat.le_floor_iff hy0).mp this
      exact_mod_cast h2
  rw [this, Finset.card_range]

section
variable (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
  (ρ : (Ω → ℝ) → ℝ)
  (hM : AxiomM (L1Plus P) ρ) (hA : IsAdditiveOn (L1Plus P) ρ) (hLI : AxiomLI P (L1Plus P) ρ)

include hP hM hA hLI in
lemma rho_bounded (X : Ω → ℝ) (hX : X ∈ L1Plus P) (M : ℕ) (hXM : ∀ ω, X ω ≤ M) :
    ρ X = ρ (I Set.univ) * ∫ ω, X ω ∂P := by
  set lam := ρ (I Set.univ) with hlam
  have lam_nonneg : 0 ≤ lam := rho_nonneg P ρ hM hA (I_mem P _ MeasurableSet.univ)
  have hB : ∀ n k : ℕ, MeasurableSet {ω | ((k:ℝ) + 1) / 2 ^ n ≤ X ω} :=
    fun n k => measurableSet_le measurable_const hX.1.1
  set S : ℕ → Ω → ℝ := fun n => ∑ k ∈ Finset.range (M * 2 ^ n),
    (1 / (2:ℝ) ^ n) • I {ω | ((k:ℝ) + 1) / 2 ^ n ≤ X ω} with hS
  have hSmem : ∀ n, S n ∈ L1Plus P := fun n =>
    sum_mem P _ _ fun k _ => smul_mem P (I_mem P _ (hB n k)) _ (by positivity)
  have hSρ : ∀ n, ρ (S n) = lam * ∫ ω, S n ω ∂P := by
    intro n
    simp only [hS]
    rw [rho_sum P ρ hA _ _ fun k _ => smul_mem P (I_mem P _ (hB n k)) _ (by positivity)]
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ fun k _ => (I_mem P _ (hB n k)).1.2.smul (1 / (2:ℝ) ^ n)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [rho_smul P ρ hM hA (I_mem P _ (hB n k)) _ (by positivity),
      rho_I P hP ρ hM hA hLI _ (hB n k)]
    simp only [Pi.smul_apply]
    rw [integral_smul, integral_I P _ (hB n k), smul_eq_mul]
    ring
  have hSval : ∀ n ω, S n ω = (⌊(2:ℝ) ^ n * X ω⌋₊ : ℝ) / 2 ^ n := by
    intro n ω
    simp only [hS, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    have h2n : (0:ℝ) < 2 ^ n := by positivity
    have : ∀ k ∈ Finset.range (M * 2 ^ n), I {ω | ((k:ℝ) + 1) / 2 ^ n ≤ X ω} ω =
        if ((k:ℝ) + 1) ≤ 2 ^ n * X ω then 1 else 0 := by
      intro k _
      unfold I
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      congr 1
      apply propext
      rw [div_le_iff₀ h2n, mul_comm]
    rw [Finset.sum_congr rfl this, Finset.sum_boole]
    rw [card_filter_le (M * 2 ^ n) _ (by have := hX.2 ω; positivity)
      (by push_cast; have := hXM ω; nlinarith)]
    ring
  have hSle : ∀ n ω, S n ω ≤ X ω := by
    intro n ω
    rw [hSval, div_le_iff₀ (by positivity), mul_comm]
    exact Nat.floor_le (by have := hX.2 ω; positivity)
  have hSge : ∀ n ω, X ω - 1 / 2 ^ n ≤ S n ω := by
    intro n ω
    rw [hSval]
    have h2n : (0:ℝ) < 2 ^ n := by positivity
    have := Nat.lt_floor_add_one ((2:ℝ) ^ n * X ω)
    rw [show X ω - 1 / 2 ^ n = (2 ^ n * X ω - 1) / 2 ^ n by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) h2n.le
  have hconst : ∀ c : ℝ, 0 ≤ c → ρ (c • I Set.univ) = c * lam := fun c hc =>
    rho_smul P ρ hM hA (I_mem P _ MeasurableSet.univ) c hc
  have key : ∀ n : ℕ, |ρ X - lam * ∫ ω, X ω ∂P| ≤ lam * (1 / 2 ^ n) := by
    intro n
    have hint1 : ∫ ω, S n ω ∂P ≤ ∫ ω, X ω ∂P :=
      integral_mono (hSmem n).1.2 hX.1.2 (hSle n)
    have hint2 : ∫ ω, X ω ∂P - 1 / 2 ^ n ≤ ∫ ω, S n ω ∂P := by
      have := integral_mono (hX.1.2.sub (integrable_const (1 / (2:ℝ) ^ n))) (hSmem n).1.2
        (fun ω => hSge n ω)
      rw [show (X - fun _ => 1 / (2:ℝ) ^ n) = fun ω => X ω - 1 / (2:ℝ) ^ n from rfl,
        integral_sub hX.1.2 (integrable_const _), integral_const] at this
      simpa using this
    have lo : ρ (S n) ≤ ρ X := hM _ (hSmem n) _ hX (hSle n)
    have hmem2 : S n + (1 / (2:ℝ) ^ n) • I Set.univ ∈ L1Plus P :=
      add_mem P (hSmem n) (smul_mem P (I_mem P _ MeasurableSet.univ) _ (by positivity))
    have hi : ρ X ≤ ρ (S n + (1 / (2:ℝ) ^ n) • I Set.univ) := by
      apply hM _ hX _ hmem2
      intro ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, I, Set.indicator_univ, mul_one]
      linarith [hSge n ω]
    rw [hA _ (hSmem n) _ (smul_mem P (I_mem P _ MeasurableSet.univ) _ (by positivity)),
      hconst _ (by positivity), hSρ] at hi
    rw [hSρ] at lo
    rw [abs_le]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hint2 lam_nonneg]
    · nlinarith [mul_le_mul_of_nonneg_left hint1 lam_nonneg]
  have hlim : Tendsto (fun n : ℕ => lam * (1 / (2:ℝ) ^ n)) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => (1 / (2:ℝ)) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [one_div_pow] using this.const_mul lam
  have := ge_of_tendsto' hlim key
  have h0 := abs_nonneg (ρ X - lam * ∫ ω, X ω ∂P)
  have : |ρ X - lam * ∫ ω, X ω ∂P| = 0 := le_antisymm (by linarith) h0
  rw [abs_eq_zero, sub_eq_zero] at this
  exact this

end

end ESAxA1Aux

namespace ESAxA1Aux

open ESAxioms.Characterization ESAxAtomless

variable {Ω : Type*} [MeasurableSpace Ω]

lemma map_eq_of_sameLaw (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (h : SameLaw P X Y) : P.map X = P.map Y := by
  have _h1 : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply hX measurableSet_Iic, Measure.map_apply hY measurableSet_Iic,
    ← ofReal_measureReal (μ := P) (s := X ⁻¹' Set.Iic x),
    ← ofReal_measureReal (μ := P) (s := Y ⁻¹' Set.Iic x)]
  have := h x
  simp only [TailRiskSharing.VaRConv.distFn] at this
  exact congrArg ENNReal.ofReal this

lemma integral_eq_of_sameLaw (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (h : SameLaw P X Y) :
    ∫ ω, X ω ∂P = ∫ ω, Y ω ∂P := by
  have e := map_eq_of_sameLaw P X Y hX hY h
  have h1 : ∫ x, x ∂(P.map X) = ∫ ω, X ω ∂P := integral_map hX.aemeasurable aestronglyMeasurable_id
  have h2 : ∫ x, x ∂(P.map Y) = ∫ ω, Y ω ∂P := integral_map hY.aemeasurable aestronglyMeasurable_id
  rw [← h1, ← h2, e]

section
variable (P : Measure Ω) [IsProbabilityMeasure P] (hP : TailRiskSharing.VaRConv.IsAtomless P)
  (ρ : (Ω → ℝ) → ℝ)
  (hM : AxiomM (L1Plus P) ρ) (hA : IsAdditiveOn (L1Plus P) ρ) (hLI : AxiomLI P (L1Plus P) ρ)

include hM hA hLI in
/-- Automatic boundedness of a positive additive law-invariant functional. -/
lemma rho_bound : ∃ C : ℝ, ∀ Y ∈ L1Plus P, ρ Y ≤ C * ∫ ω, Y ω ∂P := by
  by_contra h
  push Not at h
  choose Y hY hYρ using fun n : ℕ => h ((4:ℝ) ^ n)
  have hEpos : ∀ n, 0 < ∫ ω, Y n ω ∂P := by
    intro n
    by_contra hle
    push Not at hle
    have h0 : ∫ ω, Y n ω ∂P = 0 := le_antisymm hle (integral_nonneg (hY n).2)
    have hae : Y n =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg (hY n).2 (hY n).1.2).mp h0
    have := hLI _ (hY n) 0 (zero_mem P) (sameLaw_of_ae P hae)
    have := hYρ n
    rw [h0, mul_zero, ‹ρ (Y n) = ρ 0›, rho_zero P ρ hA] at this
    exact lt_irrefl _ this
  set c : ℕ → ℝ := fun n => 1 / (2 ^ n * ∫ ω, Y n ω ∂P) with hc
  have hcpos : ∀ n, 0 < c n := fun n => by have := hEpos n; positivity
  set Z : ℕ → Ω → ℝ := fun n => c n • Y n with hZdef
  have hZ : ∀ n, Z n ∈ L1Plus P := fun n => smul_mem P (hY n) _ (hcpos n).le
  have hZint : ∀ n, ∫ ω, Z n ω ∂P = (1/2) ^ n := by
    intro n
    simp only [hZdef, Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul, hc]
    have := (hEpos n).ne'
    field_simp
    rw [← mul_pow]; norm_num
  have hZρ : ∀ n, (2:ℝ) ^ n < ρ (Z n) := by
    intro n
    rw [hZdef, rho_smul P ρ hM hA (hY n) _ (hcpos n).le]
    have h1 := mul_lt_mul_of_pos_left (hYρ n) (hcpos n)
    have h2 : c n * ((4:ℝ) ^ n * ∫ ω, Y n ω ∂P) = 2 ^ n := by
      rw [hc]
      have := (hEpos n).ne'
      rw [show (4:ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
      field_simp
    linarith
  set f : ℕ → Ω → ENNReal := fun n ω => ENNReal.ofReal (Z n ω) with hf
  have hfm : ∀ n, Measurable (f n) := fun n => ENNReal.measurable_ofReal.comp (hZ n).1.1
  have hlint : ∫⁻ ω, ∑' n, f n ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun n => (hfm n).aemeasurable]
    have : ∀ n, ∫⁻ ω, f n ω ∂P = (2⁻¹ : ENNReal) ^ n := by
      intro n
      simp only [hf]
      rw [← ofReal_integral_eq_lintegral_ofReal (hZ n).1.2 (Eventually.of_forall (hZ n).2),
        hZint n, ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos]
      simp
    simp only [this]
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]; simp
  set D : Set Ω := {ω | ∑' n, f n ω = ⊤} with hDdef
  have hDm : MeasurableSet D :=
    measurableSet_eq_fun (Measurable.ennreal_tsum hfm) measurable_const
  have hD0 : P D = 0 := by
    have := ae_lt_top (Measurable.ennreal_tsum hfm) hlint
    rw [ae_iff] at this
    have e : {a | ¬∑' n, f n a < ⊤} = D := by ext ω; simp [hDdef]
    rwa [e] at this
  set Z' : ℕ → Ω → ℝ := fun n => Dᶜ.indicator (Z n) with hZ'def
  have hZ' : ∀ n, Z' n ∈ L1Plus P := fun n =>
    ⟨⟨(hZ n).1.1.indicator hDm.compl, (hZ n).1.2.indicator hDm.compl⟩,
      fun ω => Set.indicator_nonneg (fun ω _ => (hZ n).2 ω) ω⟩
  have hZ'ae : ∀ n, Z' n =ᵐ[P] Z n := by
    intro n
    have : ∀ᵐ ω ∂P, ω ∈ Dᶜ := compl_mem_ae_iff.mpr hD0
    filter_upwards [this] with ω hω
    simp only [hZ'def, Set.indicator_of_mem hω]
  have hZ'ρ : ∀ n, ρ (Z' n) = ρ (Z n) := fun n =>
    hLI _ (hZ' n) _ (hZ n) (sameLaw_of_ae P (hZ'ae n))
  set W : Ω → ℝ := fun ω => (∑' n, ENNReal.ofReal (Z' n ω)).toReal with hWdef
  have hWm : Measurable W := ENNReal.measurable_toReal.comp
    (Measurable.ennreal_tsum fun n => ENNReal.measurable_ofReal.comp (hZ' n).1.1)
  have hWint : Integrable W P := by
    apply integrable_toReal_of_lintegral_ne_top
      (Measurable.ennreal_tsum fun n => ENNReal.measurable_ofReal.comp (hZ' n).1.1).aemeasurable
    refine ne_top_of_le_ne_top hlint (lintegral_mono fun ω => ENNReal.tsum_le_tsum fun n => ?_)
    apply ENNReal.ofReal_le_ofReal
    simp only [hZ'def]
    exact Set.indicator_le_self' (fun ω _ => (hZ n).2 ω) ω
  have hW : W ∈ L1Plus P := ⟨⟨hWm, hWint⟩, fun ω => ENNReal.toReal_nonneg⟩
  have hpartial : ∀ N : ℕ, ∀ ω, (∑ n ∈ Finset.range N, Z' n) ω ≤ W ω := by
    intro N ω
    rw [Finset.sum_apply]
    by_cases hω : ω ∈ D
    · have : ∀ n, Z' n ω = 0 := fun n => by
        simp only [hZ'def]; exact Set.indicator_of_notMem (show ω ∉ Dᶜ from fun h => h hω) _
      simp only [this, Finset.sum_const_zero]
      exact ENNReal.toReal_nonneg
    · have hval : ∀ n, Z' n ω = Z n ω := fun n => by
        simp only [hZ'def]; exact Set.indicator_of_mem hω _
      have hfin : ∑' n, f n ω ≠ ⊤ := hω
      simp only [hWdef, hval]
      have : ∑ n ∈ Finset.range N, Z n ω = (∑ n ∈ Finset.range N, f n ω).toReal := by
        rw [ENNReal.toReal_sum (fun n _ => ENNReal.ofReal_ne_top)]
        apply Finset.sum_congr rfl
        intro n _
        exact (ENNReal.toReal_ofReal ((hZ n).2 ω)).symm
      rw [this]
      exact ENNReal.toReal_mono hfin (ENNReal.sum_le_tsum _)
  obtain ⟨N, hN⟩ := exists_nat_gt (ρ W)
  have h1 := hM _ (sum_mem P _ _ fun n _ => hZ' n) _ hW (hpartial N)
  rw [rho_sum P ρ hA _ _ fun n _ => hZ' n] at h1
  have h2 : (N:ℝ) ≤ ∑ n ∈ Finset.range N, ρ (Z' n) := by
    have : ∑ n ∈ Finset.range N, (1:ℝ) ≤ ∑ n ∈ Finset.range N, ρ (Z' n) := by
      apply Finset.sum_le_sum
      intro n _
      rw [hZ'ρ]
      have := hZρ n
      have : (1:ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      linarith
    simpa using this
  linarith

include hP hM hA hLI in
theorem a1_forward : ∀ X ∈ L1Plus P, ρ X = ρ (I Set.univ) * ∫ ω, X ω ∂P := by
  set lam := ρ (I Set.univ) with hlam
  obtain ⟨C, hC⟩ := rho_bound P ρ hM hA hLI
  intro X hX
  set m : ℕ → Ω → ℝ := fun n ω => min (X ω) n with hm
  set r : ℕ → Ω → ℝ := fun n ω => max (X ω - n) 0 with hr
  have hmmem : ∀ n, m n ∈ L1Plus P := fun n =>
    ⟨⟨hX.1.1.min measurable_const, hX.1.2.inf (integrable_const _)⟩,
      fun ω => le_min (hX.2 ω) (Nat.cast_nonneg n)⟩
  have hrmem : ∀ n, r n ∈ L1Plus P := by
    intro n
    refine ⟨⟨(hX.1.1.sub measurable_const).max measurable_const, ?_⟩, fun ω => le_max_right _ _⟩
    refine Integrable.mono' hX.1.2 ((hX.1.1.sub measurable_const).max measurable_const).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    simp only [hr, Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    have := hX.2 ω
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    exact max_le (by linarith) (hX.2 ω)
  have hsplit : ∀ n, X = m n + r n := by
    intro n; funext ω
    simp only [hm, hr, Pi.add_apply]
    rcases le_total (X ω) n with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  have hρ : ∀ n, ρ X = lam * ∫ ω, m n ω ∂P + ρ (r n) := by
    intro n
    conv_lhs => rw [hsplit n]
    rw [hA _ (hmmem n) _ (hrmem n), rho_bounded P hP ρ hM hA hLI (m n) (hmmem n) n
      (fun ω => min_le_right _ _)]
  have hint : ∀ n, ∫ ω, r n ω ∂P = ∫ ω, X ω ∂P - ∫ ω, m n ω ∂P := by
    intro n
    have := congrArg (fun f => ∫ ω, f ω ∂P) (hsplit n)
    simp only [Pi.add_apply] at this
    rw [integral_add (hmmem n).1.2 (hrmem n).1.2] at this
    linarith
  have hlim : Tendsto (fun n : ℕ => ∫ ω, m n ω ∂P) atTop (𝓝 (∫ ω, X ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence X (fun n => (hmmem n).1.1.aestronglyMeasurable)
      hX.1.2
    · intro n
      refine Eventually.of_forall fun ω => ?_
      simp only [hm, Real.norm_eq_abs]
      rw [abs_of_nonneg (le_min (hX.2 ω) (Nat.cast_nonneg n))]
      exact min_le_left _ _
    · refine Eventually.of_forall fun ω => ?_
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ⌈X ω⌉₊] with n hn
      simp only [hm]
      rw [min_eq_left]
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hlo : ∀ n, lam * ∫ ω, m n ω ∂P ≤ ρ X := fun n => by
    rw [hρ n]; linarith [rho_nonneg P ρ hM hA (hrmem n)]
  have hhi : ∀ n, ρ X ≤ lam * ∫ ω, m n ω ∂P + C * (∫ ω, X ω ∂P - ∫ ω, m n ω ∂P) := fun n => by
    rw [hρ n, ← hint n]; linarith [hC _ (hrmem n)]
  have t1 : Tendsto (fun n : ℕ => lam * ∫ ω, m n ω ∂P) atTop (𝓝 (lam * ∫ ω, X ω ∂P)) :=
    hlim.const_mul lam
  have t2 : Tendsto (fun n : ℕ => lam * ∫ ω, m n ω ∂P + C * (∫ ω, X ω ∂P - ∫ ω, m n ω ∂P))
      atTop (𝓝 (lam * ∫ ω, X ω ∂P + C * (∫ ω, X ω ∂P - ∫ ω, X ω ∂P))) :=
    t1.add ((tendsto_const_nhds.sub hlim).const_mul C)
  rw [sub_self, mul_zero, add_zero] at t2
  exact le_antisymm (ge_of_tendsto' t2 hhi) (le_of_tendsto' t1 hlo)

end

theorem lemmaA1 (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (ρ : (Ω → ℝ) → ℝ) :
    (AxiomM (L1Plus P) ρ ∧ IsAdditiveOn (L1Plus P) ρ ∧ AxiomLI P (L1Plus P) ρ) ↔
      ∃ c : ℝ, 0 ≤ c ∧ ∀ X ∈ L1Plus P, ρ X = c * ∫ ω, X ω ∂P := by
  constructor
  · rintro ⟨hM, hA, hLI⟩
    exact ⟨ρ (I Set.univ), rho_nonneg P ρ hM hA (I_mem P _ MeasurableSet.univ),
      a1_forward P hP ρ hM hA hLI⟩
  · rintro ⟨c, hc, hρ⟩
    refine ⟨?_, ?_, ?_⟩
    · intro X hX Y hY hXY
      rw [hρ X hX, hρ Y hY]
      exact mul_le_mul_of_nonneg_left (integral_mono hX.1.2 hY.1.2 hXY) hc
    · intro X hX Y hY
      rw [hρ X hX, hρ Y hY, hρ _ (add_mem P hX hY)]
      simp only [Pi.add_apply]
      rw [integral_add hX.1.2 hY.1.2]; ring
    · intro X hX Y hY hXY
      rw [hρ X hX, hρ Y hY, integral_eq_of_sameLaw P X Y hX.1.1 hY.1.1 hXY]

end ESAxA1Aux

namespace ESAxA2Aux

open ESAxioms.Characterization ESAxP1Aux ESAxAtomless ESAxReal ESAxA3Aux ESAxP4Aux ESAxESF
  ESAxA1Aux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma ind_preimage (G : Set Ω) (W : Ω → ℝ) (S : Set ℝ) :
    G.indicator W ⁻¹' S = (G ∩ W ⁻¹' S) ∪ (Gᶜ ∩ {_ω | (0:ℝ) ∈ S}) := by
  ext ω
  by_cases h : ω ∈ G
  · simp [h, Set.indicator_of_mem h]
  · simp [h, Set.indicator_of_notMem h]

lemma ind_measure (P : Measure Ω) (G : Set Ω) (hG : MeasurableSet G) (W : Ω → ℝ) (S : Set ℝ) :
    P (G.indicator W ⁻¹' S) = P (G ∩ W ⁻¹' S) + P (Gᶜ ∩ {_ω | (0:ℝ) ∈ S}) := by
  rw [ind_preimage]
  apply measure_union _ (hG.compl.inter (MeasurableSet.const _))
  exact Set.disjoint_left.mpr fun ω h1 h2 => h2.1 h1.1

lemma map_ind_eq (P : Measure Ω) (G G' : Set Ω) (hG : MeasurableSet G) (hG' : MeasurableSet G')
    (W W' : Ω → ℝ) (hW : Measurable W) (hW' : Measurable W')
    (h : ∀ S, MeasurableSet S → P (G ∩ W ⁻¹' S) = P (G' ∩ W' ⁻¹' S)) (hc : P Gᶜ = P G'ᶜ) :
    P.map (G.indicator W) = P.map (G'.indicator W') := by
  ext S hS
  rw [Measure.map_apply (hW.indicator hG) hS, Measure.map_apply (hW'.indicator hG') hS,
    ind_measure P G hG W S, ind_measure P G' hG' W' S, h S hS]
  congr 1
  by_cases h0 : (0:ℝ) ∈ S
  · have e1 : Gᶜ ∩ {_ω : Ω | (0:ℝ) ∈ S} = Gᶜ := by ext; simp [h0]
    have e2 : G'ᶜ ∩ {_ω : Ω | (0:ℝ) ∈ S} = G'ᶜ := by ext; simp [h0]
    rw [e1, e2, hc]
  · have e1 : Gᶜ ∩ {_ω : Ω | (0:ℝ) ∈ S} = ∅ := by ext; simp [h0]
    have e2 : G'ᶜ ∩ {_ω : Ω | (0:ℝ) ∈ S} = ∅ := by ext; simp [h0]
    rw [e1, e2]

lemma sameLaw_of_map_eq (P : Measure Ω) (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V)
    (h : P.map U = P.map V) : SameLaw P U V := by
  intro x
  simp only [TailRiskSharing.VaRConv.distFn]
  show P.real (U ⁻¹' Set.Iic x) = P.real (V ⁻¹' Set.Iic x)
  rw [← map_measureReal_apply hU measurableSet_Iic, ← map_measureReal_apply hV measurableSet_Iic, h]

lemma map_smul_eq (P : Measure Ω) (U V : Ω → ℝ) (hU : Measurable U) (hV : Measurable V)
    (h : P.map U = P.map V) (s : ℝ) : P.map (fun ω => s * U ω) = P.map (fun ω => s * V ω) := by
  have e1 : (fun ω => s * U ω) = (fun y => s * y) ∘ U := rfl
  have e2 : (fun ω => s * V ω) = (fun y => s * y) ∘ V := rfl
  rw [e1, e2, ← Measure.map_map (measurable_const_mul s) hU,
    ← Measure.map_map (measurable_const_mul s) hV, h]

lemma ind_integrable (P : Measure Ω) [IsProbabilityMeasure P] (G : Set Ω) (hG : MeasurableSet G)
    (W Z : Ω → ℝ) (hW : Measurable W) (hZ : Z ∈ L1 P)
    (h : ∀ S, MeasurableSet S → P (G ∩ W ⁻¹' S) = P G * P (Z ⁻¹' S)) :
    Integrable (G.indicator W) P := by
  have hmap : (P.restrict G).map W = P G • P.map Z := by
    ext S hS
    rw [Measure.map_apply hW hS, Measure.restrict_apply (hW hS), Measure.smul_apply,
      Measure.map_apply hZ.1 hS, Set.inter_comm, h S hS, smul_eq_mul]
  have h1 : Integrable id (P.map Z) :=
    (integrable_map_measure aestronglyMeasurable_id hZ.1.aemeasurable).mpr hZ.2
  have h2 : Integrable id ((P.restrict G).map W) := by
    rw [hmap]; exact h1.smul_measure (measure_ne_top P G)
  have h3 : Integrable W (P.restrict G) :=
    (integrable_map_measure aestronglyMeasurable_id hW.aemeasurable).mp h2
  exact (integrable_indicator_iff hG).mpr h3

/-- Realizing a single law on an event. -/
lemma exists_copy (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (G : Set Ω) (hG : MeasurableSet G) (hG0 : P G ≠ 0)
    (Z : Ω → ℝ) :
    ∃ W : Ω → ℝ, Measurable Z → (Measurable W ∧
      ∀ S, MeasurableSet S → P (G ∩ W ⁻¹' S) = P G * P (Z ⁻¹' S)) := by
  by_cases hZ : Measurable Z
  · have _hpm : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
    obtain ⟨W, hW, hlaw⟩ := exists_realization P hP G hG hG0 (P.map Z)
    exact ⟨W, fun _ => ⟨hW, fun S hS => by rw [hlaw S hS, Measure.map_apply hZ hS]⟩⟩
  · exact ⟨0, fun h => absurd h hZ⟩

/-- Realizing a pair law on an event. -/
lemma exists_copy2 (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (G : Set Ω) (hG : MeasurableSet G) (hG0 : P G ≠ 0)
    (Z1 Z2 : Ω → ℝ) (h1 : Measurable Z1) (h2 : Measurable Z2) :
    ∃ V1 V2 : Ω → ℝ, Measurable V1 ∧ Measurable V2 ∧
      ∀ g : ℝ × ℝ → ℝ, Measurable g → ∀ S, MeasurableSet S →
        P (G ∩ (fun ω => g (V1 ω, V2 ω)) ⁻¹' S) = P G * P ((fun ω => g (Z1 ω, Z2 ω)) ⁻¹' S) := by
  have hZ : Measurable (fun ω => (Z1 ω, Z2 ω)) := h1.prodMk h2
  have _hpm : IsProbabilityMeasure (P.map (fun ω => (Z1 ω, Z2 ω))) :=
    Measure.isProbabilityMeasure_map hZ.aemeasurable
  obtain ⟨V, hV, hlaw⟩ := exists_realization P hP G hG hG0 (P.map (fun ω => (Z1 ω, Z2 ω)))
  refine ⟨fun ω => (V ω).1, fun ω => (V ω).2, measurable_fst.comp hV, measurable_snd.comp hV,
    fun g hg S hS => ?_⟩
  have := hlaw (g ⁻¹' S) (hg hS)
  rw [Measure.map_apply hZ (hg hS)] at this
  exact this

lemma ae_nonneg_of_law (P : Measure Ω) (G : Set Ω) (V Z : Ω → ℝ)
    (h : ∀ S, MeasurableSet S → P (G ∩ V ⁻¹' S) = P G * P (Z ⁻¹' S)) (hZ : ∀ ω, 0 ≤ Z ω) :
    ∀ᵐ ω ∂P, ω ∈ G → 0 ≤ V ω := by
  rw [ae_iff]
  have e : {ω | ¬(ω ∈ G → 0 ≤ V ω)} = G ∩ V ⁻¹' Set.Iio 0 := by ext ω; simp
  rw [e, h _ measurableSet_Iio]
  have : Z ⁻¹' Set.Iio 0 = ∅ := by
    ext ω; simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hZ ω
  rw [this, measure_empty, mul_zero]

lemma sind_mem (P : Measure Ω) [IsProbabilityMeasure P] (G : Set Ω) (hG : MeasurableSet G) (s : ℝ)
    (V Z : Ω → ℝ) (hV : Measurable V) (hZ : Z ∈ L1 P)
    (h : ∀ S, MeasurableSet S → P (G ∩ V ⁻¹' S) = P G * P (Z ⁻¹' S)) :
    (fun ω => s * G.indicator V ω) ∈ L1 P :=
  ⟨(hV.indicator hG).const_mul s, (ind_integrable P G hG V Z hV hZ h).const_mul s⟩

/-- Transfer: `ρ(s 1_G V)` only depends on the law of `V` on `G` (and on `ℙ(G)`). -/
lemma transfer (P : Measure Ω) [IsProbabilityMeasure P] (ρ : (Ω → ℝ) → ℝ)
    (hLI : AxiomLI P (L1 P) ρ) (G : Set Ω) (hG : MeasurableSet G) (s : ℝ) (G' : Set Ω) (hG' : MeasurableSet G') (V V' Z Z' : Ω → ℝ) (hV : Measurable V)
    (hV' : Measurable V') (hZ : Z ∈ L1 P) (hZ' : Z' ∈ L1 P)
    (h : ∀ S, MeasurableSet S → P (G ∩ V ⁻¹' S) = P G * P (Z ⁻¹' S))
    (h' : ∀ S, MeasurableSet S → P (G' ∩ V' ⁻¹' S) = P G' * P (Z' ⁻¹' S))
    (hGG : P G = P G') (hZZ : P.map Z = P.map Z') :
    ρ (fun ω => s * G.indicator V ω) = ρ (fun ω => s * G'.indicator V' ω) := by
  apply hLI _ (sind_mem P G hG s V Z hV hZ h) _ (sind_mem P G' hG' s V' Z' hV' hZ' h')
  apply sameLaw_of_map_eq P _ _ ((hV.indicator hG).const_mul s) ((hV'.indicator hG').const_mul s)
  apply map_smul_eq P _ _ (hV.indicator hG) (hV'.indicator hG')
  apply map_ind_eq P G G' hG hG' V V' hV hV'
  · intro S hS
    rw [h S hS, h' S hS, hGG, ← Measure.map_apply hZ.1 hS, ← Measure.map_apply hZ'.1 hS, hZZ]
  · rw [prob_compl_eq_one_sub hG, prob_compl_eq_one_sub hG', hGG]

end ESAxA2Aux

namespace ESAxA7Aux

open ESAxioms.Characterization ESAxP1Aux ESAxA3Aux ESAxESF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Key comparison: for any `A` with `ℙ(A) = 1 - p` and a `p`-tail event `B`, the function
`D = (X - xₚ)(1_A - 1_B)` is `≤ 0` a.s. -/
theorem lemmaA7 (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (X : Ω → ℝ) (hX : X ∈ L1 P) (A : Set Ω) (hA : MeasurableSet A) (hPA : P.real A = 1 - p) :
    ES P p X = condExpOn P X A ↔ IsPTailEvent P p X A := by
  have hp1 : (1 - p) ≠ 0 := by linarith [hp.2]
  constructor
  · intro hES
    obtain ⟨B, hB⟩ := (lemmaA3 P hP p hp X hX.1).2
    obtain ⟨-, hB1, hB2⟩ := ((lemmaA3 P hP p hp X hX.1).1 B hB.1.1).mp hB
    have hBm := hB.1.1
    set x := VaR P p X with hx
    have hESB := ES_tail P hP p hp X hX B hB
    have hIA : ∫ ω in A, X ω ∂P = (1 - p) * ES P p X := by
      rw [hES]; unfold condExpOn; rw [hPA]; field_simp
    set V : Ω → ℝ := fun ω => X ω - x with hV
    have hVi : Integrable V P := hX.2.sub (integrable_const x)
    set D : Ω → ℝ := fun ω => A.indicator V ω - B.indicator V ω with hD
    have hDi : Integrable D P := (hVi.indicator hA).sub (hVi.indicator hBm)
    have hDint : ∫ ω, D ω ∂P = 0 := by
      simp only [hD]
      rw [integral_sub (hVi.indicator hA) (hVi.indicator hBm), integral_indicator hA,
        integral_indicator hBm]
      simp only [hV]
      rw [integral_sub hX.2.integrableOn (integrable_const x),
        integral_sub hX.2.integrableOn (integrable_const x), setIntegral_const, setIntegral_const,
        hIA, ← hESB, hPA, hB.2]
      ring
    have hDle : ∀ᵐ ω ∂P, D ω ≤ 0 := by
      filter_upwards [hB1, hB2] with ω h1 h2
      simp only [hD, hV]
      by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B
      · rw [Set.indicator_of_mem hωA, Set.indicator_of_mem hωB]; simp
      · rw [Set.indicator_of_mem hωA, Set.indicator_of_notMem hωB]
        have : X ω ≤ x := by by_contra h; push Not at h; exact hωB (h1 h)
        linarith
      · rw [Set.indicator_of_notMem hωA, Set.indicator_of_mem hωB]
        have : x ≤ X ω := h2 hωB
        linarith
      · rw [Set.indicator_of_notMem hωA, Set.indicator_of_notMem hωB]; simp
    have hD0 : D =ᵐ[P] 0 := by
      have h0 : 0 ≤ᵐ[P] -D := by
        filter_upwards [hDle] with ω hω
        simp only [Pi.zero_apply, Pi.neg_apply]; linarith
      have hint : ∫ ω, (-D) ω ∂P = 0 := by
        simp only [Pi.neg_apply]; rw [integral_neg, hDint, neg_zero]
      have := (integral_eq_zero_iff_of_nonneg_ae h0 hDi.neg).mp hint
      filter_upwards [this] with ω hω
      simp only [Pi.neg_apply, Pi.zero_apply] at hω ⊢
      linarith
    apply ((lemmaA3 P hP p hp X hX.1).1 A hA).mpr
    refine ⟨hPA, ?_, ?_⟩
    · show ∀ᵐ ω ∂P, ω ∈ {ω | x < X ω} → ω ∈ A
      filter_upwards [hD0, hB1] with ω hω h1 hgt
      have hωB : ω ∈ B := h1 hgt
      by_contra hωA
      simp only [hD, hV, Pi.zero_apply, Set.indicator_of_notMem hωA,
        Set.indicator_of_mem hωB] at hω
      have hgt' : x < X ω := hgt
      linarith
    · show ∀ᵐ ω ∂P, ω ∈ A → ω ∈ {ω | x ≤ X ω}
      filter_upwards [hD0, hB2] with ω hω h2 hωA
      by_cases hωB : ω ∈ B
      · exact h2 hωB
      · simp only [hD, hV, Pi.zero_apply, Set.indicator_of_mem hωA,
          Set.indicator_of_notMem hωB] at hω
        show x ≤ X ω
        linarith
  · intro hT
    have := ES_tail P hP p hp X hX A hT
    unfold condExpOn
    rw [hPA, ← this]
    field_simp

end ESAxA7Aux


namespace ESAxT1Aux

open ESAxioms.Characterization

variable {Ω : Type*} [MeasurableSpace Ω]

lemma VaR_eq (P : Measure Ω) (q : ℝ) (X : Ω → ℝ) :
    VaR P q X = sInf {x | q ≤ TailRiskSharing.VaRConv.distFn P X x} := by
  simp [VaR, TailRiskSharing.VaRConv.VaRL]

/-- VaR of a nonpositive variable that is negative with probability at most `p`. -/
lemma VaR_nonpos_zero (P : Measure Ω) [IsProbabilityMeasure P] (p q : ℝ) (hpq : p < q)
    (hq : q ≤ 1) (Y : Ω → ℝ) (hY : ∀ ω, Y ω ≤ 0) (hneg : P.real {ω | Y ω < 0} ≤ p) :
    VaR P q Y = 0 := by
  rw [VaR_eq]
  apply IsLeast.csInf_eq
  refine ⟨?_, ?_⟩
  · show q ≤ P.real {ω | Y ω ≤ 0}
    have : {ω | Y ω ≤ 0} = Set.univ := Set.eq_univ_of_forall hY
    rw [this, probReal_univ]; exact hq
  · intro x hx
    by_contra hlt
    push Not at hlt
    have h1 : TailRiskSharing.VaRConv.distFn P Y x ≤ P.real {ω | Y ω < 0} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      linarith
    have : q ≤ TailRiskSharing.VaRConv.distFn P Y x := hx
    linarith

lemma ES_nonpos_zero (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (Y : Ω → ℝ) (hY : ∀ ω, Y ω ≤ 0) (hneg : P.real {ω | Y ω < 0} ≤ p) :
    ES P p Y = 0 := by
  unfold ES
  have : ∫ q in Set.Ioo p 1, VaR P q Y = ∫ q in Set.Ioo p 1, (0:ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro q hq
    exact VaR_nonpos_zero P p q hq.1 hq.2.le Y hY hneg
  rw [this]; simp

lemma VaR_const (P : Measure Ω) [IsProbabilityMeasure P] (q c : ℝ) (hq0 : 0 < q) (hq : q ≤ 1) :
    VaR P q (fun _ => c) = c := by
  rw [VaR_eq]
  apply IsLeast.csInf_eq
  refine ⟨?_, ?_⟩
  · show q ≤ P.real {ω : Ω | c ≤ c}
    simp; exact hq
  · intro x hx
    by_contra hlt
    push Not at hlt
    have : q ≤ P.real {ω : Ω | c ≤ x} := hx
    have h2 : {ω : Ω | c ≤ x} = ∅ := by
      ext ω; simp; linarith
    rw [h2] at this; simp at this; linarith

lemma ES_const (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (c : ℝ) : ES P p (fun _ => c) = c := by
  unfold ES
  have : ∫ q in Set.Ioo p 1, VaR P q (fun _ => c) = ∫ q in Set.Ioo p 1, c := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro q hq
    exact VaR_const P q c (lt_trans hp.1 hq.1) hq.2.le
  rw [this, setIntegral_const]
  rw [Real.volume_real_Ioo_of_le hp.2.le]
  have : (1 - p) ≠ 0 := by linarith [hp.2]
  simp only [smul_eq_mul]
  field_simp

lemma VaR_indicator (P : Measure Ω) [IsProbabilityMeasure P] (B : Set Ω) (hB : MeasurableSet B)
    (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1) :
    VaR P q (B.indicator (fun _ => (1:ℝ))) = (Set.Ioi (1 - P.real B)).indicator (fun _ => (1:ℝ)) q := by
  rw [VaR_eq]
  have hc : P.real Bᶜ = 1 - P.real B := probReal_compl_eq_one_sub hB
  by_cases hqs : 1 - P.real B < q
  · rw [Set.indicator_of_mem (by exact hqs)]
    apply IsLeast.csInf_eq
    refine ⟨?_, ?_⟩
    · show q ≤ P.real {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ 1}
      have : {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ 1} = Set.univ := by
        ext ω; by_cases h : ω ∈ B <;> simp [h]
      rw [this, probReal_univ]; exact hq
    · intro x hx
      by_contra hlt
      push Not at hlt
      have hx' : q ≤ P.real {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ x} := hx
      have h1 : P.real {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ x} ≤ P.real Bᶜ := by
        refine measureReal_mono ?_ (measure_ne_top _ _)
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω
        intro hωB
        rw [Set.indicator_of_mem hωB] at hω
        linarith
      linarith
  · push Not at hqs
    rw [Set.indicator_of_notMem (by simpa using hqs)]
    apply IsLeast.csInf_eq
    refine ⟨?_, ?_⟩
    · show q ≤ P.real {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ 0}
      have : {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ 0} = Bᶜ := by
        ext ω; by_cases h : ω ∈ B <;> simp [h]
      rw [this, hc]; exact hqs
    · intro x hx
      by_contra hlt
      push Not at hlt
      have hx' : q ≤ P.real {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ x} := hx
      have : {ω | B.indicator (fun _ => (1:ℝ)) ω ≤ x} = ∅ := by
        ext ω; by_cases h : ω ∈ B <;> simp [h] <;> linarith
      rw [this] at hx'; simp at hx'; linarith

lemma ES_indicator (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (B : Set Ω) (hB : MeasurableSet B) (hs : P.real B ≤ 1 - p) :
    ES P p (B.indicator (fun _ => (1:ℝ))) = P.real B / (1 - p) := by
  unfold ES
  have : ∫ q in Set.Ioo p 1, VaR P q (B.indicator (fun _ => (1:ℝ))) =
      ∫ q in Set.Ioo p 1, (Set.Ioi (1 - P.real B)).indicator (fun _ => (1:ℝ)) q := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro q hq
    exact VaR_indicator P B hB q (lt_trans hp.1 hq.1) hq.2.le
  rw [this, setIntegral_indicator measurableSet_Ioi]
  have hI : Set.Ioo p 1 ∩ Set.Ioi (1 - P.real B) = Set.Ioo (1 - P.real B) 1 := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Ioi]; constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
  have hB0 : 0 ≤ P.real B := measureReal_nonneg
  rw [hI, setIntegral_const, Real.volume_real_Ioo_of_le (by linarith)]
  have : (1 - p) ≠ 0 := by linarith [hp.2]
  simp only [smul_eq_mul, mul_one]
  field_simp
  ring

/-- Halving: an atomless probability space has events of arbitrarily small positive probability. -/
lemma exists_small (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (n : ℕ) :
    ∃ B : Set Ω, MeasurableSet B ∧ 0 < P.real B ∧ P.real B ≤ (1/2 : ℝ) ^ n := by
  induction n with
  | zero => exact ⟨Set.univ, MeasurableSet.univ, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨B, hB, hpos, hle⟩ := ih
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
    · refine ⟨t, ht, ht0', ?_⟩
      rw [pow_succ]; linarith
    · refine ⟨B \ t, hB.diff ht, by rw [hd]; linarith, ?_⟩
      rw [hd, pow_succ]; push Not at h; linarith

lemma const_mem_L1 (P : Measure Ω) [IsProbabilityMeasure P] (c : ℝ) :
    (fun _ : Ω => c) ∈ L1 P := ⟨measurable_const, integrable_const c⟩

lemma ind_mem_L1 (P : Measure Ω) [IsProbabilityMeasure P] (B : Set Ω) (hB : MeasurableSet B)
    (c : ℝ) : (fun ω => c * B.indicator (fun _ => (1:ℝ)) ω) ∈ L1 P :=
  ⟨(measurable_const.indicator hB).const_mul c, ((integrable_const (1:ℝ)).indicator hB).const_mul c⟩

/-- Proof of Theorem 1, (⇒), p. 22: if `ρ = a𝔼 + b ESₚ` on `L¹` is monotone, prudent and
normalized, then `a = 0` and `b = 1`. -/
lemma core (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (ρ : (Ω → ℝ) → ℝ) (h1 : ρ (fun _ => 1) = 1) (hM : AxiomM (L1 P) ρ) (hPr : AxiomP (L1 P) ρ)
    (a b : ℝ) (hab : ∀ X ∈ L1 P, ρ X = a * ∫ ω, X ω ∂P + b * ES P p X) :
    ∀ X ∈ L1 P, ρ X = ES P p X := by
  -- normalization
  have hsum : a + b = 1 := by
    have := hab _ (const_mem_L1 P 1)
    rw [h1, ES_const P p hp] at this
    simp at this; linarith
  have h0 : ρ (fun _ => 0) = 0 := by
    rw [hab _ (const_mem_L1 P 0), ES_const P p hp]; simp
  -- small events
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hp.1 (by norm_num : (1/2:ℝ) < 1)
  choose B hBm hBpos hBle using fun k : ℕ => exists_small P hP (k + m)
  have hBp : ∀ k, P.real (B k) < p := by
    intro k
    have : (1/2:ℝ) ^ (k + m) ≤ (1/2) ^ m :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith [hBle k]
  have hBi : ∀ k, P (B k) ≤ (2⁻¹ : ENNReal) ^ k := by
    intro k
    rw [← ofReal_measureReal (μ := P) (s := B k)]
    have : P.real (B k) ≤ (1/2:ℝ) ^ k := by
      have : (1/2:ℝ) ^ (k + m) ≤ (1/2) ^ k :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith [hBle k]
    calc ENNReal.ofReal (P.real (B k)) ≤ ENNReal.ofReal ((1/2:ℝ) ^ k) := ENNReal.ofReal_le_ofReal this
      _ = (2⁻¹ : ENNReal) ^ k := by
        rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos]
        simp
  have hsumB : ∑' i, P (B i) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hBi)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]; simp
  set N : Set Ω := ⋂ n, ⋃ i ≥ n, B i with hN
  have hNm : MeasurableSet N :=
    MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hBm i
  have hN0 : P N = 0 := by
    have := measure_limsup_atTop_eq_zero (μ := P) hsumB
    rw [limsup_eq_iInf_iSup_of_nat] at this
    simpa [hN, Set.iInf_eq_iInter, Set.iSup_eq_iUnion] using this
  have hN0' : P.real N = 0 := by simp [measureReal_def, hN0]
  -- the sequence ξₖ = -(ℙ Bₖ)⁻¹ 1_{Bₖ \ N}
  set ξ : ℕ → Ω → ℝ := fun k ω => -(P.real (B k))⁻¹ * (B k \ N).indicator (fun _ => (1:ℝ)) ω
    with hξ
  have hξL1 : ∀ k, ξ k ∈ L1 P := fun k => ind_mem_L1 P _ ((hBm k).diff hNm) _
  have hξE : ∀ k, ∫ ω, ξ k ω ∂P = -1 := by
    intro k
    simp only [hξ]
    rw [integral_const_mul, integral_indicator_const _ ((hBm k).diff hNm),
      measureReal_sdiff_null hN0']
    have := (hBpos k).ne'
    simp only [smul_eq_mul, mul_one]
    field_simp
  have hξle : ∀ k ω, ξ k ω ≤ 0 := by
    intro k ω
    simp only [hξ]
    have hc : 0 ≤ (P.real (B k))⁻¹ := inv_nonneg.mpr (hBpos k).le
    have hi : 0 ≤ (B k \ N).indicator (fun _ => (1:ℝ)) ω :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    nlinarith
  have hξES : ∀ k, ES P p (ξ k) = 0 := by
    intro k
    apply ES_nonpos_zero P p hp _ (hξle k)
    have hsub : {ω | ξ k ω < 0} ⊆ B k := by
      intro ω hω
      by_contra hn
      simp only [Set.mem_setOf_eq, hξ] at hω
      rw [Set.indicator_of_notMem (fun h => hn h.1)] at hω
      simp at hω
    have := measureReal_mono (μ := P) hsub (measure_ne_top _ _)
    linarith [hBp k]
  have hρξ : ∀ k, ρ (ξ k) = -a := by
    intro k
    rw [hab _ (hξL1 k), hξE k, hξES k]; ring
  -- a ≥ 0 by monotonicity
  have ha0 : 0 ≤ a := by
    have := hM (ξ 0) (hξL1 0) _ (const_mem_L1 P 0) (hξle 0)
    rw [hρξ 0, h0] at this; linarith
  -- a ≤ 0 by prudence
  have ha1 : a ≤ 0 := by
    have hconv : ∀ ω, Tendsto (fun k => ξ k ω) atTop (𝓝 ((fun _ : Ω => (0:ℝ)) ω)) := by
      intro ω
      apply tendsto_const_nhds.congr'
      by_cases hω : ω ∈ N
      · exact Filter.Eventually.of_forall fun k => by
          simp only [hξ]; rw [Set.indicator_of_notMem (fun h => h.2 hω)]; simp
      · simp only [hN, Set.mem_iInter, not_forall] at hω
        obtain ⟨n, hn⟩ := hω
        simp only [Set.mem_iUnion, not_exists] at hn
        rw [Filter.EventuallyEq, Filter.eventually_atTop]
        refine ⟨n, fun k hk => ?_⟩
        simp only [hξ]
        rw [Set.indicator_of_notMem (fun h => hn k hk h.1)]; simp
    have := hPr ξ (fun _ => 0) hξL1 (const_mem_L1 P 0) hconv (-a)
      (by simp only [hρξ]; exact tendsto_const_nhds)
    rw [h0] at this; linarith
  have ha : a = 0 := le_antisymm ha1 ha0
  have hb : b = 1 := by linarith
  intro X hX
  rw [hab X hX, ha, hb]; ring

lemma Lq_one (P : Measure Ω) : Lq P 1 = L1 P := by
  ext X; simp [Lq, L1, memLp_one_iff_integrable]

/-- Uniqueness of `p`: `ESₚ = ES_{p'}` on `L¹` forces `p = p'` (atomless space). -/
lemma ES_inj (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p p' : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1)
    (hp' : p' ∈ Set.Ioo (0:ℝ) 1) (h : ∀ X ∈ L1 P, ES P p X = ES P p' X) : p = p' := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (lt_min (sub_pos.mpr hp.2) (sub_pos.mpr hp'.2))
    (by norm_num : (1/2:ℝ) < 1)
  obtain ⟨B, hB, hpos, hle⟩ := exists_small P hP m
  have h1 : P.real B ≤ 1 - p := by linarith [min_le_left (1 - p) (1 - p')]
  have h2 : P.real B ≤ 1 - p' := by linarith [min_le_right (1 - p) (1 - p')]
  have hX : B.indicator (fun _ => (1:ℝ)) ∈ L1 P :=
    ⟨measurable_const.indicator hB, (integrable_const (1:ℝ)).indicator hB⟩
  have := h _ hX
  rw [ES_indicator P p hp B hB h1, ES_indicator P p' hp' B hB h2] at this
  have hne : (1 - p) ≠ 0 := by linarith [hp.2]
  have hne' : (1 - p') ≠ 0 := by linarith [hp'.2]
  rw [div_eq_div_iff hne hne'] at this
  have := mul_left_cancel₀ hpos.ne' this
  linarith

end ESAxT1Aux

namespace ESAxT5Aux

open ESAxioms.Characterization ESAxP1Aux ESAxAtomless ESAxReal ESAxA3Aux ESAxP4Aux ESAxESF
  ESAxA1Aux ESAxA7Aux

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `𝔼[X 1_A] ≤ (1 - p) ESₚ(X)` whenever `ℙ(A) = 1 - p`. -/
lemma int_le_ES (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (X : Ω → ℝ) (hX : X ∈ L1 P) (A : Set Ω) (hA : MeasurableSet A) (hPA : P.real A = 1 - p) :
    ∫ ω in A, X ω ∂P ≤ (1 - p) * ES P p X := by
  obtain ⟨B, hB⟩ := (lemmaA3 P hP p hp X hX.1).2
  obtain ⟨-, hB1, hB2⟩ := ((lemmaA3 P hP p hp X hX.1).1 B hB.1.1).mp hB
  have hBm := hB.1.1
  set x := VaR P p X with hx
  have hESB := ES_tail P hP p hp X hX B hB
  set V : Ω → ℝ := fun ω => X ω - x with hV
  have hVi : Integrable V P := hX.2.sub (integrable_const x)
  set D : Ω → ℝ := fun ω => A.indicator V ω - B.indicator V ω with hD
  have hDle : ∀ᵐ ω ∂P, D ω ≤ 0 := by
    filter_upwards [hB1, hB2] with ω h1 h2
    simp only [hD, hV]
    by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B
    · rw [Set.indicator_of_mem hωA, Set.indicator_of_mem hωB]; simp
    · rw [Set.indicator_of_mem hωA, Set.indicator_of_notMem hωB]
      have : X ω ≤ x := by by_contra h; push Not at h; exact hωB (h1 h)
      linarith
    · rw [Set.indicator_of_notMem hωA, Set.indicator_of_mem hωB]
      have : x ≤ X ω := h2 hωB
      linarith
    · rw [Set.indicator_of_notMem hωA, Set.indicator_of_notMem hωB]; simp
  have hDint : ∫ ω, D ω ∂P = ∫ ω in A, X ω ∂P - ∫ ω in B, X ω ∂P := by
    simp only [hD]
    rw [integral_sub (hVi.indicator hA) (hVi.indicator hBm), integral_indicator hA,
      integral_indicator hBm]
    simp only [hV]
    rw [integral_sub hX.2.integrableOn (integrable_const x),
      integral_sub hX.2.integrableOn (integrable_const x), setIntegral_const, setIntegral_const,
      hPA, hB.2]
    ring
  have := integral_nonpos_of_ae hDle
  rw [hDint] at this
  linarith

lemma sum_L1 (P : Measure Ω) {n : ℕ} (Xs : Fin n → Ω → ℝ) (h : ∀ i, Xs i ∈ L1 P) :
    (fun ω => ∑ i, Xs i ω) ∈ L1 P :=
  ⟨Finset.measurable_sum _ fun i _ => (h i).1, integrable_finset_sum _ fun i _ => (h i).2⟩

lemma setIntegral_sum (P : Measure Ω) {n : ℕ} (Xs : Fin n → Ω → ℝ) (h : ∀ i, Xs i ∈ L1 P)
    (B : Set Ω) : ∫ ω in B, (∑ i, Xs i ω) ∂P = ∑ i, ∫ ω in B, Xs i ω ∂P :=
  integral_finsetSum _ fun i _ => (h i).2.integrableOn

lemma ES_subadd (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    {n : ℕ} (Xs : Fin n → Ω → ℝ) (h : ∀ i, Xs i ∈ L1 P) :
    ES P p (fun ω => ∑ i, Xs i ω) ≤ ∑ i, ES P p (Xs i) := by
  have hS := sum_L1 P Xs h
  obtain ⟨B, hB⟩ := (lemmaA3 P hP p hp _ hS.1).2
  have h1 := ES_tail P hP p hp _ hS B hB
  rw [setIntegral_sum P Xs h B] at h1
  have h2 : ∑ i, ∫ ω in B, Xs i ω ∂P ≤ ∑ i, (1 - p) * ES P p (Xs i) :=
    Finset.sum_le_sum fun i _ => int_le_ES P hP p hp (Xs i) (h i) B hB.1.1 hB.2
  rw [← Finset.mul_sum] at h2
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  nlinarith

lemma conc_add (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    {n : ℕ} (Xs : Fin n → Ω → ℝ) (h : ∀ i, Xs i ∈ L1 P) (A : Set Ω) (hAm : MeasurableSet A)
    (hA0 : 0 < P.real A) (hA1 : P.real A < 1) (hPA : P.real A = 1 - p)
    (hA : ∀ i, IsPTailEvent P p (Xs i) A) :
    ES P p (fun ω => ∑ i, Xs i ω) = ∑ i, ES P p (Xs i) := by
  have hS := sum_L1 P Xs h
  have hSA : IsPTailEvent P p (fun ω => ∑ i, Xs i ω) A := by
    refine ⟨⟨hAm, hA0, hA1, ?_⟩, hPA⟩
    have := ae_all_iff.mpr fun i => (hA i).1.2.2.2
    filter_upwards [this] with z hz h1 h2
    exact Finset.sum_le_sum fun i _ => hz i h1 h2
  have h1 := ES_tail P hP p hp _ hS A hSA
  rw [setIntegral_sum P Xs h A] at h1
  have h2 : ∀ i, ∫ ω in A, Xs i ω ∂P = (1 - p) * ES P p (Xs i) := fun i =>
    (ES_tail P hP p hp (Xs i) (h i) A (hA i)).symm
  simp only [h2] at h1
  rw [← Finset.mul_sum] at h1
  have hp1 : (1 - p) ≠ 0 := by linarith [hp.2]
  exact mul_left_cancel₀ hp1 h1

/-- A copy of `X` with the prescribed `p`-tail event `A`. -/
lemma tail_copy (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (X : Ω → ℝ) (hX : Measurable X) (A : Set Ω) (hAm : MeasurableSet A)
    (hPA : P.real A = 1 - p) :
    ∃ X' : Ω → ℝ, Measurable X' ∧ P.map X' = P.map X ∧ IsPTailEvent P p X' A := by
  obtain ⟨B, hB⟩ := (lemmaA3 P hP p hp X hX).2
  obtain ⟨-, h1, h2⟩ := ((lemmaA3 P hP p hp X hX).1 B hB.1.1).mp hB
  have hBm := hB.1.1
  have hPB := hB.2
  set x := VaR P p X with hx
  have hp0 := hp.1
  have hp1 := hp.2
  have hPAB : P A = P B := by
    rw [← ofReal_measureReal (μ := P) (s := A), ← ofReal_measureReal (μ := P) (s := B), hPA, hPB]
  have hPAcBc : P Aᶜ = P Bᶜ := by
    rw [prob_compl_eq_one_sub hAm, prob_compl_eq_one_sub hBm, hPAB]
  have hPB0 : P B ≠ 0 := by
    intro h; rw [measureReal_def, h] at hPB; simp at hPB; linarith
  have hPBc0 : P Bᶜ ≠ 0 := by
    intro h
    have : P.real Bᶜ = 0 := by rw [measureReal_def, h]; simp
    rw [probReal_compl_eq_one_sub hBm, hPB] at this; linarith
  have hPA0 : P A ≠ 0 := by rw [hPAB]; exact hPB0
  have hPAc0 : P Aᶜ ≠ 0 := by rw [hPAcBc]; exact hPBc0
  set ν1 : Measure ℝ := (P B)⁻¹ • (P.restrict B).map X
  set ν2 : Measure ℝ := (P Bᶜ)⁻¹ • (P.restrict Bᶜ).map X
  have hν1 : ∀ S, MeasurableSet S → ν1 S = (P B)⁻¹ * P (X ⁻¹' S ∩ B) := by
    intro S hS
    simp only [ν1, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply hX hS, Measure.restrict_apply (hX hS)]
  have hν2 : ∀ S, MeasurableSet S → ν2 S = (P Bᶜ)⁻¹ * P (X ⁻¹' S ∩ Bᶜ) := by
    intro S hS
    simp only [ν2, Measure.smul_apply, smul_eq_mul]
    rw [Measure.map_apply hX hS, Measure.restrict_apply (hX hS)]
  have hν1p : IsProbabilityMeasure ν1 := ⟨by
    rw [hν1 _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter,
      ENNReal.inv_mul_cancel hPB0 (measure_ne_top _ _)]⟩
  have hν2p : IsProbabilityMeasure ν2 := ⟨by
    rw [hν2 _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter,
      ENNReal.inv_mul_cancel hPBc0 (measure_ne_top _ _)]⟩
  obtain ⟨Z1, hZ1, hZ1law⟩ := exists_realization P hP A hAm hPA0 ν1
  obtain ⟨Z2, hZ2, hZ2law⟩ := exists_realization P hP Aᶜ hAm.compl hPAc0 ν2
  classical
  set Z : Ω → ℝ := A.piecewise Z1 Z2 with hZdef
  have hZ : Measurable Z := Measurable.piecewise hAm hZ1 hZ2
  have keyA : ∀ S, MeasurableSet S → P (A ∩ Z ⁻¹' S) = P (B ∩ X ⁻¹' S) := by
    intro S hS
    have : A ∩ Z ⁻¹' S = A ∩ Z1 ⁻¹' S := by
      ext ω; simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hZdef, Set.piecewise_eq_of_mem _ _ _ h1] at h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hZdef, Set.piecewise_eq_of_mem _ _ _ h1]⟩
    rw [this, hZ1law S hS, hν1 S hS, hPAB, ← mul_assoc,
      ENNReal.mul_inv_cancel hPB0 (measure_ne_top _ _), one_mul, Set.inter_comm]
  have keyAc : ∀ S, MeasurableSet S → P (Aᶜ ∩ Z ⁻¹' S) = P (Bᶜ ∩ X ⁻¹' S) := by
    intro S hS
    have : Aᶜ ∩ Z ⁻¹' S = Aᶜ ∩ Z2 ⁻¹' S := by
      ext ω; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hZdef, Set.piecewise_eq_of_notMem _ _ _ h1] at h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by rwa [hZdef, Set.piecewise_eq_of_notMem _ _ _ h1]⟩
    rw [this, hZ2law S hS, hν2 S hS, hPAcBc, ← mul_assoc,
      ENNReal.mul_inv_cancel hPBc0 (measure_ne_top _ _), one_mul, Set.inter_comm]
  have hmap : P.map Z = P.map X := by
    ext S hS
    rw [Measure.map_apply hZ hS, Measure.map_apply hX hS,
      ← measure_inter_add_sdiff (Z ⁻¹' S) hAm, ← measure_inter_add_sdiff (X ⁻¹' S) hBm]
    have f1 : Z ⁻¹' S ∩ A = A ∩ Z ⁻¹' S := Set.inter_comm _ _
    have f2 : Z ⁻¹' S \ A = Aᶜ ∩ Z ⁻¹' S := by rw [Set.sdiff_eq, Set.inter_comm]
    have f3 : X ⁻¹' S ∩ B = B ∩ X ⁻¹' S := Set.inter_comm _ _
    have f4 : X ⁻¹' S \ B = Bᶜ ∩ X ⁻¹' S := by rw [Set.sdiff_eq, Set.inter_comm]
    rw [f1, f2, f3, f4, keyA S hS, keyAc S hS]
  refine ⟨Z, hZ, hmap, ⟨hAm, by rw [hPA]; linarith, by rw [hPA]; linarith,
    tail_of_threshold P Z A x ?_ ?_⟩, hPA⟩
  · rw [ae_iff]
    have hS : MeasurableSet (Set.Iio x) := measurableSet_Iio
    have e1 : {ω | ¬(ω ∈ A → x ≤ Z ω)} = A ∩ Z ⁻¹' Set.Iio x := by ext ω; simp
    have e2 : B ∩ X ⁻¹' Set.Iio x = {ω | ¬(ω ∈ B → x ≤ X ω)} := by ext ω; simp
    rw [e1, keyA _ hS, e2, ← ae_iff]
    exact h2
  · rw [ae_iff]
    have hS : MeasurableSet (Set.Ioi x) := measurableSet_Ioi
    have e1 : {ω | ¬(ω ∉ A → Z ω ≤ x)} = Aᶜ ∩ Z ⁻¹' Set.Ioi x := by ext ω; simp
    have e2 : Bᶜ ∩ X ⁻¹' Set.Ioi x = {ω | ¬(ω ∉ B → X ω ≤ x)} := by ext ω; simp
    rw [e1, keyAc _ hS, e2, ← ae_iff]
    filter_upwards [h1] with ω hω hωB
    by_contra hc; push Not at hc; exact hωB (hω hc)

theorem t5 (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    {n : ℕ} (Xs : Fin n → Ω → ℝ) (hXs : ∀ i, Xs i ∈ L1 P) :
    List.TFAE [IsPConcentrated P p Xs, MaximizesESAggregation P p Xs,
      ES P p (fun ω => ∑ i, Xs i ω) = ∑ i, ES P p (Xs i)] := by
  have hp0 := hp.1
  have hp1 := hp.2
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hES0 : ES P p (fun ω => ∑ i : Fin 0, Xs i ω) = 0 := by
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact ESAxT1Aux.ES_const P p hp 0
    apply List.tfae_of_forall True
    intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · simp only [iff_true]; exact ⟨∅, fun i => i.elim0⟩
    · simp only [iff_true]
      intro Xs' _ _
      have : ES P p (fun ω => ∑ i : Fin 0, Xs' i ω) = 0 := by
        simp only [Finset.univ_eq_empty, Finset.sum_empty]
        exact ESAxT1Aux.ES_const P p hp 0
      rw [this, hES0]
    · simp only [iff_true]; rw [hES0]; simp
  have hS := sum_L1 P Xs hXs
  have h13 : IsPConcentrated P p Xs → ES P p (fun ω => ∑ i, Xs i ω) = ∑ i, ES P p (Xs i) := by
    rintro ⟨A, hA⟩
    have h0 := hA ⟨0, hn⟩
    exact conc_add P hP p hp Xs hXs A h0.1.1 h0.1.2.1 h0.1.2.2.1 h0.2 hA
  tfae_have 1 → 3 := h13
  tfae_have 3 → 1 := by
    intro h3
    obtain ⟨B, hB⟩ := (lemmaA3 P hP p hp _ hS.1).2
    have h1 := ES_tail P hP p hp _ hS B hB
    rw [setIntegral_sum P Xs hXs B, h3, Finset.mul_sum] at h1
    have hle : ∀ i ∈ Finset.univ, ∫ ω in B, Xs i ω ∂P ≤ (1 - p) * ES P p (Xs i) :=
      fun i _ => int_le_ES P hP p hp (Xs i) (hXs i) B hB.1.1 hB.2
    have heq := (Finset.sum_eq_sum_iff_of_le hle).mp h1.symm
    refine ⟨B, fun i => ?_⟩
    apply (lemmaA7 P hP p hp (Xs i) (hXs i) B hB.1.1 hB.2).mp
    unfold condExpOn
    rw [hB.2, heq i (Finset.mem_univ i)]
    have : (1 - p) ≠ 0 := by linarith
    field_simp
  tfae_have 1 → 2 := by
    intro h1 Xs' hm hlaw
    have hL : ∀ i, Xs' i ∈ L1 P := by
      intro i
      refine ⟨hm i, ?_⟩
      have hmap := map_eq_of_sameLaw P (Xs' i) (Xs i) (hm i) (hXs i).1 (hlaw i)
      have h1 : Integrable id (P.map (Xs i)) :=
        (integrable_map_measure aestronglyMeasurable_id (hXs i).1.aemeasurable).mpr (hXs i).2
      rw [← hmap] at h1
      exact (integrable_map_measure aestronglyMeasurable_id (hm i).aemeasurable).mp h1
    calc ES P p (fun ω => ∑ i, Xs' i ω) ≤ ∑ i, ES P p (Xs' i) := ES_subadd P hP p hp Xs' hL
      _ = ∑ i, ES P p (Xs i) := Finset.sum_congr rfl fun i _ =>
          ES_LI P p (Xs' i) (hL i) (Xs i) (hXs i) (hlaw i)
      _ = ES P p (fun ω => ∑ i, Xs i ω) := (h13 h1).symm
  tfae_have 2 → 3 := by
    intro h2
    obtain ⟨A, -, hAm, hPA⟩ := sierpinski P hP Set.univ MeasurableSet.univ (1 - p) (by linarith)
      (by rw [probReal_univ]; linarith)
    choose Xs' hXs' using fun i => tail_copy P hP p hp (Xs i) (hXs i).1 A hAm hPA
    have hm : ∀ i, Measurable (Xs' i) := fun i => (hXs' i).1
    have hlaw : ∀ i, SameLaw P (Xs' i) (Xs i) := fun i =>
      ESAxA2Aux.sameLaw_of_map_eq P _ _ (hm i) (hXs i).1 (hXs' i).2.1
    have hL : ∀ i, Xs' i ∈ L1 P := by
      intro i
      refine ⟨hm i, ?_⟩
      have h1 : Integrable id (P.map (Xs i)) :=
        (integrable_map_measure aestronglyMeasurable_id (hXs i).1.aemeasurable).mpr (hXs i).2
      rw [← (hXs' i).2.1] at h1
      exact (integrable_map_measure aestronglyMeasurable_id (hm i).aemeasurable).mp h1
    have hmax := h2 Xs' hm hlaw
    have hc := conc_add P hP p hp Xs' hL A hAm (by rw [hPA]; linarith) (by rw [hPA]; linarith)
      hPA fun i => (hXs' i).2.2
    have hsame : ∑ i, ES P p (Xs' i) = ∑ i, ES P p (Xs i) := Finset.sum_congr rfl fun i _ =>
      ES_LI P p (Xs' i) (hL i) (Xs i) (hXs i) (hlaw i)
    have hsub := ES_subadd P hP p hp Xs hXs
    linarith
  tfae_finish

end ESAxT5Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    {n : ℕ} (Xs : Fin n → Ω → ℝ) (hXs : ∀ i, Xs i ∈ ESAxioms.Characterization.L1 P) :
    List.TFAE [ESAxioms.Characterization.IsPConcentrated P p Xs,
      ESAxioms.Characterization.MaximizesESAggregation P p Xs,
      ESAxioms.Characterization.ES P p (fun ω => ∑ i, Xs i ω) =
        ∑ i, ESAxioms.Characterization.ES P p (Xs i)] :=
  ESAxT5Aux.t5 P hP p hp Xs hXs
