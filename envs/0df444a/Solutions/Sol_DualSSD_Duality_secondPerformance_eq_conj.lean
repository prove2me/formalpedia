-- Prove2me | solution 1 for DualSSD.Duality.secondPerformance_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:52:02.189534+00:00
-- url     : https://prove2.me/submissions/3bc6f35c-09a0-492e-a234-c4889188ff84

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance
import Definitions.Def_DualSSD_Duality_secondQuantile
import Definitions.Def_DualSSD_Duality_conj

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set in
/-- Quantile function (left-continuous inverse of the cdf) of a measure on `ℝ`. -/
noncomputable def dssdQ (P : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf P x}

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem dssd_bdd (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u) :
    BddBelow {x | u ≤ cdf P x} := by
  have h := (tendsto_cdf_atBot P).eventually (gt_mem_nhds hu0)
  rw [Filter.eventually_atBot] at h
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx => ?_⟩
  by_contra hlt
  exact absurd (hx0 x (le_of_lt (not_le.mp hlt))) (not_lt.mpr hx)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem dssd_nonempty (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    ({x | u ≤ cdf P x} : Set ℝ).Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop P).eventually (lt_mem_nhds hu1)).exists
  exact ⟨x, hx.le⟩

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem dssd_le_cdf_Q (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    u ≤ cdf P (dssdQ P u) := by
  have hcont : ContinuousWithinAt (cdf P) (Ici (dssdQ P u)) (dssdQ P u) :=
    (cdf P).right_continuous _
  have ht : Tendsto (cdf P) (𝓝[>] (dssdQ P u)) (𝓝 (cdf P (dssdQ P u))) :=
    hcont.mono Ioi_subset_Ici_self
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt (dssd_nonempty P hu1) hx
  exact le_trans hs (monotone_cdf P hsx.le)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem dssd_Q_le_iff (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) (x : ℝ) : dssdQ P u ≤ x ↔ u ≤ cdf P x := by
  constructor
  · intro h
    exact le_trans (dssd_le_cdf_Q P hu1) (monotone_cdf P h)
  · intro h
    exact csInf_le (dssd_bdd P hu0) h

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem dssd_Q_mono (P : Measure ℝ) [IsProbabilityMeasure P] :
    MonotoneOn (dssdQ P) (Ioo 0 1) := by
  intro u hu v hv huv
  rw [dssd_Q_le_iff P hu.1 hu.2]
  exact le_trans huv (dssd_le_cdf_Q P hv.2)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem dssd_Q_ae (P : Measure ℝ) [IsProbabilityMeasure P] :
    AEMeasurable (dssdQ P) (volume.restrict (Ioo (0:ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (dssd_Q_mono P)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem dssd_map_Q (P : Measure ℝ) [IsProbabilityMeasure P] :
    (volume.restrict (Ioo (0:ℝ) 1)).map (dssdQ P) = P := by
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply_of_aemeasurable (dssd_Q_ae P) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo, ← ofReal_cdf P x]
  have hset : dssdQ P ⁻¹' Iic x ∩ Ioo 0 1 = {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (dssd_Q_le_iff P h2.1 h2.2 x).mp h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨(dssd_Q_le_iff P h2.1 h2.2 x).mpr h1, h2⟩
  rw [hset]
  apply le_antisymm
  · calc volume {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} ≤ volume (Icc 0 (cdf P x)) :=
          measure_mono (fun u hu => ⟨hu.1.1.le, hu.2⟩)
      _ = ENNReal.ofReal (cdf P x) := by rw [Real.volume_Icc, sub_zero]
  · calc ENNReal.ofReal (cdf P x) = volume (Ioo 0 (cdf P x)) := by rw [Real.volume_Ioo, sub_zero]
      _ ≤ volume {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} := by
          apply measure_mono
          intro u hu
          exact ⟨⟨hu.1, lt_of_lt_of_le hu.2 (cdf_le_one P x)⟩, hu.2.le⟩

open MeasureTheory in
theorem dssd_shift (c : ℝ) (f : ℝ → ℝ) (S : Set ℝ) :
    ∫ u in S, f u = ∫ t in (fun t : ℝ => t + c) ⁻¹' S, f (t + c) := by
  have A : MeasurableEmbedding (fun t : ℝ => t + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have h := A.setIntegral_map (μ := volume) f S
  rw [map_add_right_eq_self] at h
  exact h

open MeasureTheory Filter in
/-- Layer cake: the second performance function is the expected shortfall `E (η - X)⁺`. -/
theorem dssd_perf_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (x : ℝ) :
    DualSSD.Shared.secondPerformance μ X x = ∫ ω, max (x - X ω) 0 ∂μ := by
  have hi : Integrable (fun ω => max (x - X ω) 0) μ := ((integrable_const x).sub hX).pos_part
  rw [DualSSD.Shared.secondPerformance,
    hi.integral_eq_integral_meas_le (Eventually.of_forall fun ω => le_max_right _ _),
    dssd_shift x (DualSSD.Shared.distFun μ X) (Set.Iic x), Set.preimage_add_const_Iic, sub_self]
  have h2 := integral_comp_neg_Ioi (0 : ℝ) (fun s => DualSSD.Shared.distFun μ X (s + x))
  rw [neg_zero] at h2
  rw [← h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [DualSSD.Shared.distFun, measureReal_def]
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, le_max_iff]
  have ht' : 0 < t := ht
  constructor
  · intro h; left; linarith
  · rintro (h | h)
    · linarith
    · linarith

open MeasureTheory ProbabilityTheory in
theorem dssd_distFun_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : AEMeasurable X P) :
    DualSSD.Shared.distFun P X = cdf (P.map X) := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  funext η
  rw [cdf_eq_real, DualSSD.Shared.distFun, measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable hX measurableSet_Iic]
  rfl

open MeasureTheory ProbabilityTheory in
theorem dssd_leftQuantile_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : AEMeasurable X P) :
    DualSSD.Duality.leftQuantile P X = dssdQ (P.map X) := by
  funext u
  rw [DualSSD.Duality.leftQuantile, dssdQ, dssd_distFun_eq P X hX]

open MeasureTheory ProbabilityTheory Set in
/-- Integral of an indicator of `Iic p` over `(0,1)` is the integral over `(0, p]`. -/
theorem dssd_ind (f : ℝ → ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    ∫ α, (Iic p).indicator f α ∂(volume.restrict (Ioo (0:ℝ) 1)) = ∫ α in Ioc 0 p, f α := by
  rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  rcases hp.2.lt_or_eq with hp1 | hp1
  · have : Iic p ∩ Ioo (0:ℝ) 1 = Ioc 0 p := by
      ext α
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨h1, h2, lt_of_le_of_lt h1 hp1⟩
    rw [this]
  · subst hp1
    have : Iic (1:ℝ) ∩ Ioo (0:ℝ) 1 = Ioo 0 1 :=
      inter_eq_right.mpr (fun a ha => mem_Iic.mpr (le_of_lt ha.2))
    rw [this, integral_Ioc_eq_integral_Ioo]

open MeasureTheory ProbabilityTheory Set in
/-- The quantile function is integrable on `(0,1)`. -/
theorem dssd_Q_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) :
    Integrable (DualSSD.Duality.leftQuantile P X) (volume.restrict (Ioo (0:ℝ) 1)) := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [dssd_leftQuantile_eq P X hX.aemeasurable]
  have h1 : Integrable (fun y : ℝ => y) (P.map X) :=
    (integrable_map_measure aestronglyMeasurable_id hX.aemeasurable).mpr hX
  rw [← dssd_map_Q (P.map X)] at h1
  exact (integrable_map_measure aestronglyMeasurable_id (dssd_Q_ae (P.map X))).mp h1

open MeasureTheory ProbabilityTheory Set in
/-- The Young gap identity: `F^(2)(η) + F^(-2)(p) - pη` as an integral over `(0,1)`. -/
theorem dssd_gap {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    DualSSD.Shared.secondPerformance P X η
        + (∫ α in (0:ℝ)..p, DualSSD.Duality.leftQuantile P X α) - p * η
      = ∫ α, (max (η - DualSSD.Duality.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.Duality.leftQuantile P X α - η) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  set Q := DualSSD.Duality.leftQuantile P X with hQdef
  have hQ : Integrable Q (volume.restrict (Ioo (0:ℝ) 1)) := dssd_Q_int P X hX
  have hQae : AEMeasurable Q (volume.restrict (Ioo (0:ℝ) 1)) := by
    rw [hQdef, dssd_leftQuantile_eq P X hX.aemeasurable]; exact dssd_Q_ae (P.map X)
  have hmap : (volume.restrict (Ioo (0:ℝ) 1)).map Q = P.map X := by
    rw [hQdef, dssd_leftQuantile_eq P X hX.aemeasurable]; exact dssd_map_Q (P.map X)
  have hcont : Continuous (fun y : ℝ => max (η - y) 0) := by fun_prop
  -- the performance function
  have hS : DualSSD.Shared.secondPerformance P X η
      = ∫ α, max (η - Q α) 0 ∂(volume.restrict (Ioo (0:ℝ) 1)) := by
    rw [dssd_perf_eq P X hX η]
    have e1 : ∫ ω, max (η - X ω) 0 ∂P = ∫ y, max (η - y) 0 ∂(P.map X) :=
      (integral_map hX.aemeasurable hcont.aestronglyMeasurable).symm
    rw [e1, ← hmap, integral_map hQae (by rw [hmap]; exact hcont.aestronglyMeasurable)]
  -- the Lorenz part
  have hp0 : (0:ℝ) ≤ p := hp.1
  have hQp : IntegrableOn Q (Ioc 0 p) := by
    have h1 : IntegrableOn Q (Ioo 0 p) :=
      (show IntegrableOn Q (Ioo (0:ℝ) 1) volume from hQ).mono_set (Ioo_subset_Ioo_right hp.2)
    exact (integrableOn_Ioc_iff_integrableOn_Ioo).mpr h1
  have hL : (∫ α in (0:ℝ)..p, Q α) - p * η
      = ∫ α, (Iic p).indicator (fun α => Q α - η) α ∂(volume.restrict (Ioo (0:ℝ) 1)) := by
    rw [dssd_ind _ hp, intervalIntegral.integral_of_le hp0,
      integral_sub hQp (integrable_const η), setIntegral_const, Real.volume_real_Ioc_of_le hp0,
      sub_zero, smul_eq_mul]
  have hi1 : Integrable (fun α => max (η - Q α) 0) (volume.restrict (Ioo (0:ℝ) 1)) :=
    ((integrable_const η).sub hQ).pos_part
  have hi2 : Integrable ((Iic p).indicator (fun α => Q α - η))
      (volume.restrict (Ioo (0:ℝ) 1)) :=
    (hQ.sub (integrable_const η)).indicator measurableSet_Iic
  rw [integral_add hi1 hi2, ← hL, hS]
  ring

open MeasureTheory ProbabilityTheory Set in
/-- Young/Fenchel inequality: `p η ≤ F^(2)(η) + F^(-2)(p)`. -/
theorem dssd_young {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    p * η ≤ DualSSD.Shared.secondPerformance P X η
        + (∫ α in (0:ℝ)..p, DualSSD.Duality.leftQuantile P X α) := by
  have h := dssd_gap P X hX η hp
  have h0 : 0 ≤ ∫ α, (max (η - DualSSD.Duality.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.Duality.leftQuantile P X α - η) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) := by
    apply integral_nonneg
    intro α
    dsimp only [Pi.zero_apply]
    by_cases hα : α ∈ Iic p
    · rw [indicator_of_mem hα]
      have := le_max_left (η - DualSSD.Duality.leftQuantile P X α) 0
      linarith
    · rw [indicator_of_notMem hα]
      have := le_max_right (η - DualSSD.Duality.leftQuantile P X α) 0
      linarith
  linarith

open MeasureTheory ProbabilityTheory Set in
/-- Equality in Young at `p = F(η)`. -/
theorem dssd_eq_at_cdf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) :
    DualSSD.Shared.distFun P X η ∈ Icc (0:ℝ) 1 ∧
    DualSSD.Shared.secondPerformance P X η
        + (∫ α in (0:ℝ)..(DualSSD.Shared.distFun P X η), DualSSD.Duality.leftQuantile P X α)
      = DualSSD.Shared.distFun P X η * η := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hF : DualSSD.Shared.distFun P X η = cdf (P.map X) η := by
    rw [dssd_distFun_eq P X hX.aemeasurable]
  have hp : DualSSD.Shared.distFun P X η ∈ Icc (0:ℝ) 1 := by
    rw [hF]; exact ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  refine ⟨hp, ?_⟩
  have h := dssd_gap P X hX η hp
  have h0 : ∫ α, (max (η - DualSSD.Duality.leftQuantile P X α) 0
          + (Iic (DualSSD.Shared.distFun P X η)).indicator
              (fun α => DualSSD.Duality.leftQuantile P X α - η) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro α hα
    rw [dssd_leftQuantile_eq P X hX.aemeasurable, hF]
    have hg := dssd_Q_le_iff (P.map X) hα.1 hα.2 η
    by_cases hαp : α ∈ Iic (cdf (P.map X) η)
    · rw [indicator_of_mem hαp]
      have h1 : dssdQ (P.map X) α ≤ η := hg.mpr hαp
      rw [max_eq_left (by linarith)]
      ring
    · rw [indicator_of_notMem hαp]
      have h1 : ¬ dssdQ (P.map X) α ≤ η := fun h => hαp (hg.mp h)
      rw [max_eq_right (by linarith [not_le.mp h1])]
      ring
  linarith

open MeasureTheory DualSSD DualSSD.Duality in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) :
    (fun η => ((Shared.secondPerformance P X η : ℝ) : EReal)) = conj (secondQuantile P X) := by
  funext η
  apply le_antisymm
  · obtain ⟨hp, e1⟩ := dssd_eq_at_cdf P X hX η
    refine le_iSup_of_le (Shared.distFun P X η) ?_
    rw [secondQuantile, if_pos hp, ← EReal.coe_sub]
    refine EReal.coe_le_coe_iff.mpr (le_of_eq ?_)
    linarith
  · refine iSup_le fun ξ => ?_
    by_cases hp : ξ ∈ Set.Icc (0:ℝ) 1
    · rw [secondQuantile, if_pos hp, ← EReal.coe_sub]
      refine EReal.coe_le_coe_iff.mpr ?_
      have := dssd_young P X hX η hp
      linarith
    · rw [secondQuantile, if_neg hp, EReal.sub_top]
      exact bot_le
