-- Prove2me | solution 1 for DualSSD.MeanRisk.hDiam_convex_posHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:28:30.631075+00:00
-- url     : https://prove2.me/submissions/1ccb54b0-8bfb-48e9-ae62-81eab40fb1bd

import Mathlib
import Definitions.Def_DualSSD_MeanRisk_gini

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set in
/-- Quantile function (left-continuous inverse of the cdf) of a measure on `ℝ`. -/
noncomputable def hdQ (P : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf P x}

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem hd_bdd (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u) :
    BddBelow {x | u ≤ cdf P x} := by
  have h := (tendsto_cdf_atBot P).eventually (gt_mem_nhds hu0)
  rw [Filter.eventually_atBot] at h
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx => ?_⟩
  by_contra hlt
  exact absurd (hx0 x (le_of_lt (not_le.mp hlt))) (not_lt.mpr hx)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem hd_nonempty (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    ({x | u ≤ cdf P x} : Set ℝ).Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop P).eventually (lt_mem_nhds hu1)).exists
  exact ⟨x, hx.le⟩

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem hd_le_cdf_Q (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    u ≤ cdf P (hdQ P u) := by
  have hcont : ContinuousWithinAt (cdf P) (Ici (hdQ P u)) (hdQ P u) :=
    (cdf P).right_continuous _
  have ht : Tendsto (cdf P) (𝓝[>] (hdQ P u)) (𝓝 (cdf P (hdQ P u))) :=
    hcont.mono Ioi_subset_Ici_self
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt (hd_nonempty P hu1) hx
  exact le_trans hs (monotone_cdf P hsx.le)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem hd_Q_le_iff (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) (x : ℝ) : hdQ P u ≤ x ↔ u ≤ cdf P x := by
  constructor
  · intro h
    exact le_trans (hd_le_cdf_Q P hu1) (monotone_cdf P h)
  · intro h
    exact csInf_le (hd_bdd P hu0) h

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem hd_Q_mono (P : Measure ℝ) [IsProbabilityMeasure P] :
    MonotoneOn (hdQ P) (Ioo 0 1) := by
  intro u hu v hv huv
  rw [hd_Q_le_iff P hu.1 hu.2]
  exact le_trans huv (hd_le_cdf_Q P hv.2)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem hd_Q_ae (P : Measure ℝ) [IsProbabilityMeasure P] :
    AEMeasurable (hdQ P) (volume.restrict (Ioo (0:ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (hd_Q_mono P)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem hd_map_Q (P : Measure ℝ) [IsProbabilityMeasure P] :
    (volume.restrict (Ioo (0:ℝ) 1)).map (hdQ P) = P := by
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply_of_aemeasurable (hd_Q_ae P) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo, ← ofReal_cdf P x]
  have hset : hdQ P ⁻¹' Iic x ∩ Ioo 0 1 = {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (hd_Q_le_iff P h2.1 h2.2 x).mp h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨(hd_Q_le_iff P h2.1 h2.2 x).mpr h1, h2⟩
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
theorem hd_shift (c : ℝ) (f : ℝ → ℝ) (S : Set ℝ) :
    ∫ u in S, f u = ∫ t in (fun t : ℝ => t + c) ⁻¹' S, f (t + c) := by
  have A : MeasurableEmbedding (fun t : ℝ => t + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have h := A.setIntegral_map (μ := volume) f S
  rw [map_add_right_eq_self] at h
  exact h

open MeasureTheory Filter in
/-- Layer cake: the second performance function is the expected shortfall `E (η - X)⁺`. -/
theorem hd_perf_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (x : ℝ) :
    DualSSD.Shared.secondPerformance μ X x = ∫ ω, max (x - X ω) 0 ∂μ := by
  have hi : Integrable (fun ω => max (x - X ω) 0) μ := ((integrable_const x).sub hX).pos_part
  rw [DualSSD.Shared.secondPerformance,
    hi.integral_eq_integral_meas_le (Eventually.of_forall fun ω => le_max_right _ _),
    hd_shift x (DualSSD.Shared.distFun μ X) (Set.Iic x), Set.preimage_add_const_Iic, sub_self]
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
theorem hd_distFun_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : AEMeasurable X P) :
    DualSSD.Shared.distFun P X = cdf (P.map X) := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  funext η
  rw [cdf_eq_real, DualSSD.Shared.distFun, measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable hX measurableSet_Iic]
  rfl

open MeasureTheory ProbabilityTheory in
theorem hd_leftQuantile_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : AEMeasurable X P) :
    DualSSD.MeanRisk.leftQuantile P X = hdQ (P.map X) := by
  funext u
  rw [DualSSD.MeanRisk.leftQuantile, hdQ, hd_distFun_eq P X hX]

open MeasureTheory ProbabilityTheory Set in
/-- Integral of an indicator of `Iic p` over `(0,1)` is the integral over `(0, p]`. -/
theorem hd_ind (f : ℝ → ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
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
theorem hd_Q_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) :
    Integrable (DualSSD.MeanRisk.leftQuantile P X) (volume.restrict (Ioo (0:ℝ) 1)) := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [hd_leftQuantile_eq P X hX.aemeasurable]
  have h1 : Integrable (fun y : ℝ => y) (P.map X) :=
    (integrable_map_measure aestronglyMeasurable_id hX.aemeasurable).mpr hX
  rw [← hd_map_Q (P.map X)] at h1
  exact (integrable_map_measure aestronglyMeasurable_id (hd_Q_ae (P.map X))).mp h1

open MeasureTheory ProbabilityTheory Set in
/-- The Young gap identity: `F^(2)(η) + F^(-2)(p) - pη` as an integral over `(0,1)`. -/
theorem hd_gap {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    DualSSD.Shared.secondPerformance P X η
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α) - p * η
      = ∫ α, (max (η - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.MeanRisk.leftQuantile P X α - η) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  set Q := DualSSD.MeanRisk.leftQuantile P X with hQdef
  have hQ : Integrable Q (volume.restrict (Ioo (0:ℝ) 1)) := hd_Q_int P X hX
  have hQae : AEMeasurable Q (volume.restrict (Ioo (0:ℝ) 1)) := by
    rw [hQdef, hd_leftQuantile_eq P X hX.aemeasurable]; exact hd_Q_ae (P.map X)
  have hmap : (volume.restrict (Ioo (0:ℝ) 1)).map Q = P.map X := by
    rw [hQdef, hd_leftQuantile_eq P X hX.aemeasurable]; exact hd_map_Q (P.map X)
  have hcont : Continuous (fun y : ℝ => max (η - y) 0) := by fun_prop
  -- the performance function
  have hS : DualSSD.Shared.secondPerformance P X η
      = ∫ α, max (η - Q α) 0 ∂(volume.restrict (Ioo (0:ℝ) 1)) := by
    rw [hd_perf_eq P X hX η]
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
    rw [hd_ind _ hp, intervalIntegral.integral_of_le hp0,
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
theorem hd_young {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    p * η ≤ DualSSD.Shared.secondPerformance P X η
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α) := by
  have h := hd_gap P X hX η hp
  have h0 : 0 ≤ ∫ α, (max (η - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.MeanRisk.leftQuantile P X α - η) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) := by
    apply integral_nonneg
    intro α
    dsimp only [Pi.zero_apply]
    by_cases hα : α ∈ Iic p
    · rw [indicator_of_mem hα]
      have := le_max_left (η - DualSSD.MeanRisk.leftQuantile P X α) 0
      linarith
    · rw [indicator_of_notMem hα]
      have := le_max_right (η - DualSSD.MeanRisk.leftQuantile P X α) 0
      linarith
  linarith

open MeasureTheory ProbabilityTheory Set in
/-- Equality in Young at `p = F(η)`. -/
theorem hd_eq_at_cdf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) :
    DualSSD.Shared.distFun P X η ∈ Icc (0:ℝ) 1 ∧
    DualSSD.Shared.secondPerformance P X η
        + (∫ α in (0:ℝ)..(DualSSD.Shared.distFun P X η), DualSSD.MeanRisk.leftQuantile P X α)
      = DualSSD.Shared.distFun P X η * η := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hF : DualSSD.Shared.distFun P X η = cdf (P.map X) η := by
    rw [hd_distFun_eq P X hX.aemeasurable]
  have hp : DualSSD.Shared.distFun P X η ∈ Icc (0:ℝ) 1 := by
    rw [hF]; exact ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  refine ⟨hp, ?_⟩
  have h := hd_gap P X hX η hp
  have h0 : ∫ α, (max (η - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic (DualSSD.Shared.distFun P X η)).indicator
              (fun α => DualSSD.MeanRisk.leftQuantile P X α - η) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro α hα
    rw [hd_leftQuantile_eq P X hX.aemeasurable, hF]
    have hg := hd_Q_le_iff (P.map X) hα.1 hα.2 η
    by_cases hαp : α ∈ Iic (cdf (P.map X) η)
    · rw [indicator_of_mem hαp]
      have h1 : hdQ (P.map X) α ≤ η := hg.mpr hαp
      rw [max_eq_left (by linarith)]
      ring
    · rw [indicator_of_notMem hαp]
      have h1 : ¬ hdQ (P.map X) α ≤ η := fun h => hαp (hg.mp h)
      rw [max_eq_right (by linarith [not_le.mp h1])]
      ring
  linarith

open MeasureTheory ProbabilityTheory Set in
/-- Equality in Young at `η = F^(-1)(p)`, `0 < p < 1`. -/
theorem hd_eq_at_Q {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    DualSSD.Shared.secondPerformance P X (DualSSD.MeanRisk.leftQuantile P X p)
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α)
      = p * DualSSD.MeanRisk.leftQuantile P X p := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hpI : p ∈ Icc (0:ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have h := hd_gap P X hX (DualSSD.MeanRisk.leftQuantile P X p) hpI
  have h0 : ∫ α, (max (DualSSD.MeanRisk.leftQuantile P X p - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.MeanRisk.leftQuantile P X α
              - DualSSD.MeanRisk.leftQuantile P X p) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro α hα
    rw [hd_leftQuantile_eq P X hX.aemeasurable]
    have hm := hd_Q_mono (P.map X)
    by_cases hαp : α ∈ Iic p
    · rw [indicator_of_mem hαp]
      have h1 : hdQ (P.map X) α ≤ hdQ (P.map X) p := hm hα hp hαp
      rw [max_eq_left (by linarith)]
      ring
    · rw [indicator_of_notMem hαp]
      have h1 : hdQ (P.map X) p ≤ hdQ (P.map X) α :=
        hm hp hα (le_of_lt (not_le.mp hαp))
      rw [max_eq_right (by linarith)]
      ring
  linarith

open MeasureTheory ProbabilityTheory Set in
/-- The absolute Lorenz curve is continuous on `[0,1]`. -/
theorem hd_L_cont {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) :
    ContinuousOn (fun p => ∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α) (Icc 0 1) := by
  have hQ := hd_Q_int P X hX
  have h1 : IntegrableOn (DualSSD.MeanRisk.leftQuantile P X) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (integrableOn_Icc_iff_integrableOn_Ioo).mpr hQ
  have h2 := intervalIntegral.continuousOn_primitive_interval h1
  rwa [uIcc_of_le zero_le_one] at h2


open MeasureTheory ProbabilityTheory Set in
theorem hd_distFun_congr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f g : Ω → ℝ}
    (h : f =ᵐ[P] g) : DualSSD.Shared.distFun P f = DualSSD.Shared.distFun P g := by
  funext η
  simp only [DualSSD.Shared.distFun, measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [h] with ω hω
  change (f ω ≤ η) = (g ω ≤ η)
  rw [hω]

open MeasureTheory ProbabilityTheory Set in
theorem hd_tailGini_congr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f g : Ω → ℝ}
    (h : f =ᵐ[P] g) (p : ℝ) :
    DualSSD.MeanRisk.tailGini P f p = DualSSD.MeanRisk.tailGini P g p := by
  have hL : DualSSD.MeanRisk.leftQuantile P f = DualSSD.MeanRisk.leftQuantile P g := by
    funext α
    simp only [DualSSD.MeanRisk.leftQuantile, hd_distFun_congr P h]
  have hm : DualSSD.MeanRisk.mean P f = DualSSD.MeanRisk.mean P g := integral_congr_ae h
  simp only [DualSSD.MeanRisk.tailGini, DualSSD.MeanRisk.secondQuantileR, hL, hm]

open MeasureTheory ProbabilityTheory Set Pointwise in
theorem hd_Q_smul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) {c : ℝ}
    (hc : 0 < c) (α : ℝ) :
    DualSSD.MeanRisk.leftQuantile P (fun ω => c * X ω) α
      = c * DualSSD.MeanRisk.leftQuantile P X α := by
  have hset : {η : ℝ | α ≤ DualSSD.Shared.distFun P (fun ω => c * X ω) η}
      = c • {η : ℝ | α ≤ DualSSD.Shared.distFun P X η} := by
    ext η
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
    simp only [Set.mem_setOf_eq, smul_eq_mul, DualSSD.Shared.distFun]
    have : {ω | c * X ω ≤ η} = {ω | X ω ≤ c⁻¹ * η} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [le_inv_mul_iff₀ hc]
    rw [this]
  rw [DualSSD.MeanRisk.leftQuantile, hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
  rfl

open MeasureTheory ProbabilityTheory Set in
theorem hd_tailGini_smul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) {c : ℝ}
    (hc : 0 < c) (p : ℝ) :
    DualSSD.MeanRisk.tailGini P (fun ω => c * X ω) p = c * DualSSD.MeanRisk.tailGini P X p := by
  have hm : DualSSD.MeanRisk.mean P (fun ω => c * X ω) = c * DualSSD.MeanRisk.mean P X :=
    integral_const_mul c X
  have hS : ∀ α, DualSSD.MeanRisk.secondQuantileR P (fun ω => c * X ω) α
      = c * DualSSD.MeanRisk.secondQuantileR P X α := by
    intro α
    simp only [DualSSD.MeanRisk.secondQuantileR, hd_Q_smul P X hc]
    exact intervalIntegral.integral_const_mul c _
  simp only [DualSSD.MeanRisk.tailGini, hm, hS]
  have : ∀ α : ℝ, c * DualSSD.MeanRisk.mean P X * α - c * DualSSD.MeanRisk.secondQuantileR P X α
      = c * (DualSSD.MeanRisk.mean P X * α - DualSSD.MeanRisk.secondQuantileR P X α) := by
    intro α; ring
  simp only [this, intervalIntegral.integral_const_mul]
  ring

open MeasureTheory ProbabilityTheory Set in
/-- Concavity of the absolute Lorenz curve in the random variable, on `(0,1)`. -/
theorem hd_L_concave_Ioo {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    a * (∫ β in (0:ℝ)..α, DualSSD.MeanRisk.leftQuantile P X β)
      + b * (∫ β in (0:ℝ)..α, DualSSD.MeanRisk.leftQuantile P Y β)
      ≤ ∫ β in (0:ℝ)..α, DualSSD.MeanRisk.leftQuantile P (fun ω => a * X ω + b * Y ω) β := by
  have hZ : Integrable (fun ω => a * X ω + b * Y ω) P := (hX.const_mul a).add (hY.const_mul b)
  have eX := hd_eq_at_Q P X hX hα
  have eY := hd_eq_at_Q P Y hY hα
  set qX := DualSSD.MeanRisk.leftQuantile P X α
  set qY := DualSSD.MeanRisk.leftQuantile P Y α
  have yZ := hd_young P (fun ω => a * X ω + b * Y ω) hZ (a * qX + b * qY) (p := α)
    ⟨hα.1.le, hα.2.le⟩
  rw [hd_perf_eq P X hX] at eX
  rw [hd_perf_eq P Y hY] at eY
  rw [hd_perf_eq P _ hZ] at yZ
  have iX : Integrable (fun ω => max (qX - X ω) 0) P := ((integrable_const qX).sub hX).pos_part
  have iY : Integrable (fun ω => max (qY - Y ω) 0) P := ((integrable_const qY).sub hY).pos_part
  have iZ : Integrable (fun ω => max (a * qX + b * qY - (a * X ω + b * Y ω)) 0) P :=
    ((integrable_const _).sub hZ).pos_part
  have hle : ∫ ω, max (a * qX + b * qY - (a * X ω + b * Y ω)) 0 ∂P
      ≤ ∫ ω, (a * max (qX - X ω) 0 + b * max (qY - Y ω) 0) ∂P := by
    apply integral_mono iZ ((iX.const_mul a).add (iY.const_mul b))
    intro ω
    show max (a * qX + b * qY - (a * X ω + b * Y ω)) 0
      ≤ a * max (qX - X ω) 0 + b * max (qY - Y ω) 0
    apply max_le
    · have h1 := mul_le_mul_of_nonneg_left (le_max_left (qX - X ω) 0) ha
      have h2 := mul_le_mul_of_nonneg_left (le_max_left (qY - Y ω) 0) hb
      linarith
    · have h1 := mul_nonneg ha (le_max_right (qX - X ω) 0)
      have h2 := mul_nonneg hb (le_max_right (qY - Y ω) 0)
      linarith
  rw [integral_add (iX.const_mul a) (iY.const_mul b), integral_const_mul, integral_const_mul]
    at hle
  have kX : a * (∫ ω, max (qX - X ω) 0 ∂P)
      = a * (α * qX) - a * (∫ β in (0:ℝ)..α, DualSSD.MeanRisk.leftQuantile P X β) := by
    rw [← eX]; ring
  have kY : b * (∫ ω, max (qY - Y ω) 0 ∂P)
      = b * (α * qY) - b * (∫ β in (0:ℝ)..α, DualSSD.MeanRisk.leftQuantile P Y β) := by
    rw [← eY]; ring
  have : α * (a * qX + b * qY) = a * (α * qX) + b * (α * qY) := by ring
  linarith

open MeasureTheory ProbabilityTheory Set in
theorem hd_g_cont {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) :
    ContinuousOn (fun α => DualSSD.MeanRisk.mean P X * α - DualSSD.MeanRisk.secondQuantileR P X α)
      (Icc 0 1) :=
  (continuousOn_const.mul continuousOn_id).sub (hd_L_cont P X hX)

open MeasureTheory ProbabilityTheory Set in
theorem hd_hDiam_congr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f g : Ω → ℝ}
    (h : f =ᵐ[P] g) (p : ℝ) :
    DualSSD.MeanRisk.hDiam P f p = DualSSD.MeanRisk.hDiam P g p := by
  have hL : DualSSD.MeanRisk.leftQuantile P f = DualSSD.MeanRisk.leftQuantile P g := by
    funext α
    simp only [DualSSD.MeanRisk.leftQuantile, hd_distFun_congr P h]
  have hm : DualSSD.MeanRisk.mean P f = DualSSD.MeanRisk.mean P g := integral_congr_ae h
  simp only [DualSSD.MeanRisk.hDiam, DualSSD.MeanRisk.secondQuantileR, hL, hm]

open MeasureTheory ProbabilityTheory Set in
theorem hd_hDiam_smul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) {c : ℝ}
    (hc : 0 < c) (p : ℝ) :
    DualSSD.MeanRisk.hDiam P (fun ω => c * X ω) p = c * DualSSD.MeanRisk.hDiam P X p := by
  have hm : DualSSD.MeanRisk.mean P (fun ω => c * X ω) = c * DualSSD.MeanRisk.mean P X :=
    integral_const_mul c X
  have hS : DualSSD.MeanRisk.secondQuantileR P (fun ω => c * X ω) p
      = c * DualSSD.MeanRisk.secondQuantileR P X p := by
    simp only [DualSSD.MeanRisk.secondQuantileR, hd_Q_smul P X hc]
    exact intervalIntegral.integral_const_mul c _
  simp only [DualSSD.MeanRisk.hDiam, hm, hS]
  ring

open MeasureTheory ProbabilityTheory Set in
theorem hd_hDiam_convex {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    DualSSD.MeanRisk.hDiam P (fun ω => a * X ω + b * Y ω) p
      ≤ a * DualSSD.MeanRisk.hDiam P X p + b * DualSSD.MeanRisk.hDiam P Y p := by
  have hZ : Integrable (fun ω => a * X ω + b * Y ω) P := (hX.const_mul a).add (hY.const_mul b)
  have hm : DualSSD.MeanRisk.mean P (fun ω => a * X ω + b * Y ω)
      = a * DualSSD.MeanRisk.mean P X + b * DualSSD.MeanRisk.mean P Y := by
    simp only [DualSSD.MeanRisk.mean]
    rw [integral_add (hX.const_mul a) (hY.const_mul b), integral_const_mul, integral_const_mul]
  set gX := fun α => DualSSD.MeanRisk.mean P X * α - DualSSD.MeanRisk.secondQuantileR P X α
  set gY := fun α => DualSSD.MeanRisk.mean P Y * α - DualSSD.MeanRisk.secondQuantileR P Y α
  set gZ := fun α => DualSSD.MeanRisk.mean P (fun ω => a * X ω + b * Y ω) * α
    - DualSSD.MeanRisk.secondQuantileR P (fun ω => a * X ω + b * Y ω) α
  have cX : ContinuousOn gX (Icc 0 1) := hd_g_cont P X hX
  have cY : ContinuousOn gY (Icc 0 1) := hd_g_cont P Y hY
  have cZ : ContinuousOn gZ (Icc 0 1) := hd_g_cont P _ hZ
  have hcl : closure (Set.Ioo (0:ℝ) 1) = Set.Icc 0 1 := closure_Ioo zero_ne_one
  have h1 : ∀ α ∈ Ioo (0:ℝ) 1, gZ α ≤ (fun α => a * gX α + b * gY α) α := by
    intro α hα
    have := hd_L_concave_Ioo P X Y hX hY ha hb hab hα
    simp only [gX, gY, gZ, hm, DualSSD.MeanRisk.secondQuantileR]
    nlinarith
  have key : gZ p ≤ a * gX p + b * gY p := by
    refine le_on_closure h1 ?_ ?_ (by rw [hcl]; exact hp)
    · rw [hcl]; exact cZ
    · rw [hcl]; exact (continuousOn_const.mul cX).add (continuousOn_const.mul cY)
  exact key

open MeasureTheory DualSSD.MeanRisk in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ConvexOn ℝ Set.univ (fun X : Lp ℝ 1 P => hDiam P (⇑X) p) ∧
      ∀ c : ℝ, 0 < c → ∀ X : Lp ℝ 1 P, hDiam P ⇑(c • X) p = c * hDiam P (⇑X) p := by
  refine ⟨⟨convex_univ, ?_⟩, ?_⟩
  · intro x _ y _ a b ha hb hab
    have hae : (⇑(a • x + b • y) : Ω → ℝ) =ᵐ[P] fun ω => a * x ω + b * y ω := by
      filter_upwards [Lp.coeFn_add (a • x) (b • y), Lp.coeFn_smul a x, Lp.coeFn_smul b y]
        with ω h1 h2 h3
      rw [h1, Pi.add_apply, h2, h3]
      rfl
    show hDiam P (⇑(a • x + b • y)) p ≤ a • hDiam P (⇑x) p + b • hDiam P (⇑y) p
    rw [hd_hDiam_congr P hae, smul_eq_mul, smul_eq_mul]
    exact hd_hDiam_convex P x y (L1.integrable_coeFn x) (L1.integrable_coeFn y) ha hb hab hp
  · intro c hc X
    have hae : (⇑(c • X) : Ω → ℝ) =ᵐ[P] fun ω => c * X ω := by
      filter_upwards [Lp.coeFn_smul c X] with ω h1
      rw [h1]
      rfl
    rw [hd_hDiam_congr P hae]
    exact hd_hDiam_smul P X hc p
