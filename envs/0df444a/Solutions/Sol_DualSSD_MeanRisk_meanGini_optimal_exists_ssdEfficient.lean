-- Prove2me | solution 1 for DualSSD.MeanRisk.meanGini_optimal_exists_ssdEfficient
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T03:03:19.546398+00:00
-- url     : https://prove2.me/submissions/ae2f72bc-f497-4121-be84-60a1ecb8e807

import Mathlib
import Definitions.Def_DualSSD_MeanRisk_gini
import Definitions.Def_DualSSD_MeanRisk_ssdEfficient
import Definitions.Def_DualSSD_Shared_secondPerformance
import Definitions.Def_DualSSD_Duality_secondQuantile

set_option autoImplicit false

/- Complete checked body: AttributedMeanGini -/
section

section
namespace GiniConsistency
-- Prove2me | solution 1 for DualSSD.MeanRisk.meanGini_ssd_consistent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T23:15:17.993072+00:00
-- url     : https://prove2.me/submissions/ec65e1be-83cb-4420-a244-94c0a319c61c


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
    DualSSD.MeanRisk.leftQuantile P X = dssdQ (P.map X) := by
  funext u
  rw [DualSSD.MeanRisk.leftQuantile, dssdQ, dssd_distFun_eq P X hX]

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
    Integrable (DualSSD.MeanRisk.leftQuantile P X) (volume.restrict (Ioo (0:ℝ) 1)) := by
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
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α) - p * η
      = ∫ α, (max (η - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.MeanRisk.leftQuantile P X α - η) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  set Q := DualSSD.MeanRisk.leftQuantile P X with hQdef
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
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α) := by
  have h := dssd_gap P X hX η hp
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
theorem dssd_eq_at_cdf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) :
    DualSSD.Shared.distFun P X η ∈ Icc (0:ℝ) 1 ∧
    DualSSD.Shared.secondPerformance P X η
        + (∫ α in (0:ℝ)..(DualSSD.Shared.distFun P X η), DualSSD.MeanRisk.leftQuantile P X α)
      = DualSSD.Shared.distFun P X η * η := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hF : DualSSD.Shared.distFun P X η = cdf (P.map X) η := by
    rw [dssd_distFun_eq P X hX.aemeasurable]
  have hp : DualSSD.Shared.distFun P X η ∈ Icc (0:ℝ) 1 := by
    rw [hF]; exact ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  refine ⟨hp, ?_⟩
  have h := dssd_gap P X hX η hp
  have h0 : ∫ α, (max (η - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic (DualSSD.Shared.distFun P X η)).indicator
              (fun α => DualSSD.MeanRisk.leftQuantile P X α - η) α)
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

open MeasureTheory ProbabilityTheory Set in
/-- Equality in Young at `η = F^(-1)(p)`, `0 < p < 1`. -/
theorem dssd_eq_at_Q {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    DualSSD.Shared.secondPerformance P X (DualSSD.MeanRisk.leftQuantile P X p)
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α)
      = p * DualSSD.MeanRisk.leftQuantile P X p := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hpI : p ∈ Icc (0:ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have h := dssd_gap P X hX (DualSSD.MeanRisk.leftQuantile P X p) hpI
  have h0 : ∫ α, (max (DualSSD.MeanRisk.leftQuantile P X p - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.MeanRisk.leftQuantile P X α
              - DualSSD.MeanRisk.leftQuantile P X p) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro α hα
    rw [dssd_leftQuantile_eq P X hX.aemeasurable]
    have hm := dssd_Q_mono (P.map X)
    by_cases hαp : α ∈ Iic p
    · rw [indicator_of_mem hαp]
      have h1 : dssdQ (P.map X) α ≤ dssdQ (P.map X) p := hm hα hp hαp
      rw [max_eq_left (by linarith)]
      ring
    · rw [indicator_of_notMem hαp]
      have h1 : dssdQ (P.map X) p ≤ dssdQ (P.map X) α :=
        hm hp hα (le_of_lt (not_le.mp hαp))
      rw [max_eq_right (by linarith)]
      ring
  linarith

open MeasureTheory ProbabilityTheory Set in
/-- The absolute Lorenz curve is continuous on `[0,1]`. -/
theorem dssd_L_cont {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) :
    ContinuousOn (DualSSD.MeanRisk.secondQuantileR P X) (Icc 0 1) := by
  have hQ := dssd_Q_int P X hX
  have h1 : IntegrableOn (DualSSD.MeanRisk.leftQuantile P X) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (integrableOn_Icc_iff_integrableOn_Ioo).mpr hQ
  have h2 := intervalIntegral.continuousOn_primitive_interval h1
  rw [uIcc_of_le zero_le_one] at h2
  exact h2

open MeasureTheory ProbabilityTheory Set DualSSD.MeanRisk in
theorem dssd_L_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P)
    (h : DualSSD.Shared.SSD P X Y) :
    ∀ p ∈ Icc (0:ℝ) 1, secondQuantileR P Y p ≤ secondQuantileR P X p := by
  intro p hp
  have key : ∀ q ∈ Ioo (0 : ℝ) 1, secondQuantileR P Y q ≤ secondQuantileR P X q := by
    intro q hq
    have e1 := dssd_eq_at_Q P Y hY hq
    have e2 := h (leftQuantile P Y q)
    have e3 := dssd_young P X hX (leftQuantile P Y q) (p := q) ⟨hq.1.le, hq.2.le⟩
    unfold secondQuantileR
    linarith
  have hcl : closure (Ioo (0:ℝ) 1) = Icc 0 1 := closure_Ioo zero_ne_one
  refine le_on_closure (f := secondQuantileR P Y) (g := secondQuantileR P X) key ?_ ?_
    (by rw [hcl]; exact hp)
  · rw [hcl]; exact dssd_L_cont P Y hY
  · rw [hcl]; exact dssd_L_cont P X hX

open MeasureTheory ProbabilityTheory Set DualSSD.MeanRisk in
theorem dssd_L_le_rev {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P)
    (h : ∀ p ∈ Icc (0:ℝ) 1, secondQuantileR P Y p ≤ secondQuantileR P X p) :
    DualSSD.Shared.SSD P X Y := by
  intro η
  obtain ⟨hp, e1⟩ := dssd_eq_at_cdf P X hX η
  have e2 := h _ hp
  unfold secondQuantileR at e2
  have e3 := dssd_young P Y hY η hp
  linarith

open MeasureTheory ProbabilityTheory Set DualSSD.MeanRisk in
/-- `μ_X − Γ_X = 2 ∫_0^1 F_X^(−2)`. -/
theorem dssd_mg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) :
    mean P X - gini P X = 2 * ∫ p in (0:ℝ)..1, secondQuantileR P X p := by
  have hL : IntervalIntegrable (secondQuantileR P X) volume 0 1 :=
    (dssd_L_cont P X hX).intervalIntegrable_of_Icc zero_le_one
  have hl : IntervalIntegrable (fun p : ℝ => mean P X * p) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  rw [gini, intervalIntegral.integral_sub hl hL, intervalIntegral.integral_const_mul, integral_id]
  ring

open MeasureTheory DualSSD DualSSD.MeanRisk in
theorem checked_meanGini_ssd_consistent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) :
    (Shared.SSD P X Y → mean P Y - gini P Y ≤ mean P X - gini P X) ∧
      (StrictSSD P X Y → mean P Y - gini P Y < mean P X - gini P X) := by
  rw [dssd_mg P X hX, dssd_mg P Y hY]
  have iX : IntervalIntegrable (secondQuantileR P X) volume 0 1 :=
    (dssd_L_cont P X hX).intervalIntegrable_of_Icc zero_le_one
  have iY : IntervalIntegrable (secondQuantileR P Y) volume 0 1 :=
    (dssd_L_cont P Y hY).intervalIntegrable_of_Icc zero_le_one
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hle := dssd_L_le P X Y hX hY h
    have := intervalIntegral.integral_mono_on zero_le_one iY iX hle
    linarith
  · obtain ⟨h1, h2⟩ := h
    have hle := dssd_L_le P X Y hX hY h1
    have hex : ∃ c ∈ Set.Icc (0:ℝ) 1, secondQuantileR P Y c < secondQuantileR P X c := by
      by_contra hne
      push Not at hne
      exact h2 (dssd_L_le_rev P Y X hY hX hne)
    have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      zero_lt_one (dssd_L_cont P Y hY) (dssd_L_cont P X hX)
      (fun x hx => hle x ⟨hx.1.le, hx.2⟩) hex
    linarith
end GiniConsistency
end

section
-- Prove2me | solution 1 for DualSSD.MeanRisk.mean_le_of_ssd
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:59:23.346746+00:00
-- url     : https://prove2.me/submissions/c0008e10-9584-42f8-91d7-525b35c8bea3


namespace DualSSD.MeanRisk

open MeasureTheory

/-- `F_X^(2)(η) = E (η - X)_+` for integrable `X`. -/
theorem aux_mlos_secondPerf_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) :
    Shared.secondPerformance P X η = ∫ ω, max (η - X ω) 0 ∂P := by
  have hf : Integrable (fun ω => max (η - X ω) 0) P := ((integrable_const η).sub hX).pos_part
  rw [hf.integral_eq_integral_meas_le (Filter.Eventually.of_forall fun _ => le_max_right _ _)]
  have h1 : ∫ t in Set.Ioi (0:ℝ), P.real {a | t ≤ max (η - X a) 0}
      = ∫ t in Set.Ioi (0:ℝ), (fun s => Shared.distFun P X (η + s)) (-t) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [Shared.distFun]
    congr 1
    ext a
    simp only [Set.mem_ofPred_eq, le_max_iff]
    have ht' : (0:ℝ) < t := ht
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h
      left
      linarith
  have h3 := integral_comp_neg_Ioi (0:ℝ) (fun s => Shared.distFun P X (η + s))
  rw [h1, h3, neg_zero]
  unfold Shared.secondPerformance
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
  have h2 : (Set.Iic (0:ℝ)).indicator (fun s => Shared.distFun P X (η + s))
      = fun s => (Set.Iic η).indicator (Shared.distFun P X) (s + η) := by
    ext s
    by_cases hs : s ≤ 0
    · have : s + η ≤ η := by linarith
      simp [Set.indicator, hs, add_comm]
    · have : ¬ (s + η ≤ η) := by intro h; exact hs (by linarith)
      simp [Set.indicator, hs, this]
  rw [h2, integral_add_right_eq_self (fun s => (Set.Iic η).indicator (Shared.distFun P X) s) η]

theorem aux_mlos_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Integrable Y P) :
    Filter.Tendsto (fun η : ℝ => ∫ ω, max (Y ω - η) 0 ∂P) Filter.atTop (nhds 0) := by
  have h0 : nhds (0:ℝ) = nhds (∫ ω, (0:ℝ) ∂P) := by simp
  rw [h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun ω => |Y ω|) ?_ ?_ hY.abs ?_
  · exact Filter.Eventually.of_forall fun η =>
      ((hY.sub (integrable_const η)).pos_part).aestronglyMeasurable
  · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with η hη
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (abs_nonneg _)
    linarith [le_abs_self (Y ω)]
  · refine Filter.Eventually.of_forall fun ω => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (Y ω)] with η hη
    rw [max_eq_right (by linarith)]

theorem aux_mlos_split {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZ : Integrable Z P) (η : ℝ) :
    ∫ ω, max (η - Z ω) 0 ∂P = η - mean P Z + ∫ ω, max (Z ω - η) 0 ∂P := by
  have e : (fun ω => max (η - Z ω) 0) = fun ω => (η - Z ω) + max (Z ω - η) 0 := by
    ext ω
    rcases le_total (Z ω) η with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  have i1 : Integrable (fun ω => η - Z ω) P := (integrable_const η).sub hZ
  have i2 : Integrable (fun ω => max (Z ω - η) 0) P := (hZ.sub (integrable_const η)).pos_part
  rw [e, integral_add i1 i2, integral_sub (integrable_const η) hZ]
  simp [mean]

end DualSSD.MeanRisk

open DualSSD.MeanRisk
open MeasureTheory

theorem checked_mean_le_of_ssd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) :
    DualSSD.Shared.SSD P X Y → mean P Y ≤ mean P X := by
  intro h
  have key : ∀ η : ℝ, mean P Y - mean P X ≤ ∫ ω, max (Y ω - η) 0 ∂P := by
    intro η
    have hη := h η
    rw [aux_mlos_secondPerf_eq P X hX η, aux_mlos_secondPerf_eq P Y hY η,
      aux_mlos_split P X hX η, aux_mlos_split P Y hY η] at hη
    have hA : 0 ≤ ∫ ω, max (X ω - η) 0 ∂P :=
      integral_nonneg fun ω => le_max_right _ _
    linarith
  have := ge_of_tendsto' (aux_mlos_tendsto P Y hY) key
  linarith
end

section
namespace GiniConvexity
-- Prove2me | solution 1 for DualSSD.MeanRisk.tailGini_convex_posHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:12:21.302904+00:00
-- url     : https://prove2.me/submissions/dafb24cf-4d0d-4e6a-be89-3966faead0cb


set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set in
/-- Quantile function (left-continuous inverse of the cdf) of a measure on `ℝ`. -/
noncomputable def tgQ (P : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf P x}

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem tg_bdd (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u) :
    BddBelow {x | u ≤ cdf P x} := by
  have h := (tendsto_cdf_atBot P).eventually (gt_mem_nhds hu0)
  rw [Filter.eventually_atBot] at h
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx => ?_⟩
  by_contra hlt
  exact absurd (hx0 x (le_of_lt (not_le.mp hlt))) (not_lt.mpr hx)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem tg_nonempty (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    ({x | u ≤ cdf P x} : Set ℝ).Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop P).eventually (lt_mem_nhds hu1)).exists
  exact ⟨x, hx.le⟩

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem tg_le_cdf_Q (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    u ≤ cdf P (tgQ P u) := by
  have hcont : ContinuousWithinAt (cdf P) (Ici (tgQ P u)) (tgQ P u) :=
    (cdf P).right_continuous _
  have ht : Tendsto (cdf P) (𝓝[>] (tgQ P u)) (𝓝 (cdf P (tgQ P u))) :=
    hcont.mono Ioi_subset_Ici_self
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt (tg_nonempty P hu1) hx
  exact le_trans hs (monotone_cdf P hsx.le)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem tg_Q_le_iff (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) (x : ℝ) : tgQ P u ≤ x ↔ u ≤ cdf P x := by
  constructor
  · intro h
    exact le_trans (tg_le_cdf_Q P hu1) (monotone_cdf P h)
  · intro h
    exact csInf_le (tg_bdd P hu0) h

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem tg_Q_mono (P : Measure ℝ) [IsProbabilityMeasure P] :
    MonotoneOn (tgQ P) (Ioo 0 1) := by
  intro u hu v hv huv
  rw [tg_Q_le_iff P hu.1 hu.2]
  exact le_trans huv (tg_le_cdf_Q P hv.2)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem tg_Q_ae (P : Measure ℝ) [IsProbabilityMeasure P] :
    AEMeasurable (tgQ P) (volume.restrict (Ioo (0:ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (tg_Q_mono P)

open MeasureTheory ProbabilityTheory Set Filter Topology in
theorem tg_map_Q (P : Measure ℝ) [IsProbabilityMeasure P] :
    (volume.restrict (Ioo (0:ℝ) 1)).map (tgQ P) = P := by
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply_of_aemeasurable (tg_Q_ae P) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo, ← ofReal_cdf P x]
  have hset : tgQ P ⁻¹' Iic x ∩ Ioo 0 1 = {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (tg_Q_le_iff P h2.1 h2.2 x).mp h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨(tg_Q_le_iff P h2.1 h2.2 x).mpr h1, h2⟩
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
theorem tg_shift (c : ℝ) (f : ℝ → ℝ) (S : Set ℝ) :
    ∫ u in S, f u = ∫ t in (fun t : ℝ => t + c) ⁻¹' S, f (t + c) := by
  have A : MeasurableEmbedding (fun t : ℝ => t + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have h := A.setIntegral_map (μ := volume) f S
  rw [map_add_right_eq_self] at h
  exact h

open MeasureTheory Filter in
/-- Layer cake: the second performance function is the expected shortfall `E (η - X)⁺`. -/
theorem tg_perf_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (x : ℝ) :
    DualSSD.Shared.secondPerformance μ X x = ∫ ω, max (x - X ω) 0 ∂μ := by
  have hi : Integrable (fun ω => max (x - X ω) 0) μ := ((integrable_const x).sub hX).pos_part
  rw [DualSSD.Shared.secondPerformance,
    hi.integral_eq_integral_meas_le (Eventually.of_forall fun ω => le_max_right _ _),
    tg_shift x (DualSSD.Shared.distFun μ X) (Set.Iic x), Set.preimage_add_const_Iic, sub_self]
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
theorem tg_distFun_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : AEMeasurable X P) :
    DualSSD.Shared.distFun P X = cdf (P.map X) := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  funext η
  rw [cdf_eq_real, DualSSD.Shared.distFun, measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable hX measurableSet_Iic]
  rfl

open MeasureTheory ProbabilityTheory in
theorem tg_leftQuantile_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : AEMeasurable X P) :
    DualSSD.MeanRisk.leftQuantile P X = tgQ (P.map X) := by
  funext u
  rw [DualSSD.MeanRisk.leftQuantile, tgQ, tg_distFun_eq P X hX]

open MeasureTheory ProbabilityTheory Set in
/-- Integral of an indicator of `Iic p` over `(0,1)` is the integral over `(0, p]`. -/
theorem tg_ind (f : ℝ → ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
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
theorem tg_Q_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) :
    Integrable (DualSSD.MeanRisk.leftQuantile P X) (volume.restrict (Ioo (0:ℝ) 1)) := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [tg_leftQuantile_eq P X hX.aemeasurable]
  have h1 : Integrable (fun y : ℝ => y) (P.map X) :=
    (integrable_map_measure aestronglyMeasurable_id hX.aemeasurable).mpr hX
  rw [← tg_map_Q (P.map X)] at h1
  exact (integrable_map_measure aestronglyMeasurable_id (tg_Q_ae (P.map X))).mp h1

open MeasureTheory ProbabilityTheory Set in
/-- The Young gap identity: `F^(2)(η) + F^(-2)(p) - pη` as an integral over `(0,1)`. -/
theorem tg_gap {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    DualSSD.Shared.secondPerformance P X η
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α) - p * η
      = ∫ α, (max (η - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.MeanRisk.leftQuantile P X α - η) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  set Q := DualSSD.MeanRisk.leftQuantile P X with hQdef
  have hQ : Integrable Q (volume.restrict (Ioo (0:ℝ) 1)) := tg_Q_int P X hX
  have hQae : AEMeasurable Q (volume.restrict (Ioo (0:ℝ) 1)) := by
    rw [hQdef, tg_leftQuantile_eq P X hX.aemeasurable]; exact tg_Q_ae (P.map X)
  have hmap : (volume.restrict (Ioo (0:ℝ) 1)).map Q = P.map X := by
    rw [hQdef, tg_leftQuantile_eq P X hX.aemeasurable]; exact tg_map_Q (P.map X)
  have hcont : Continuous (fun y : ℝ => max (η - y) 0) := by fun_prop
  -- the performance function
  have hS : DualSSD.Shared.secondPerformance P X η
      = ∫ α, max (η - Q α) 0 ∂(volume.restrict (Ioo (0:ℝ) 1)) := by
    rw [tg_perf_eq P X hX η]
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
    rw [tg_ind _ hp, intervalIntegral.integral_of_le hp0,
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
theorem tg_young {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    p * η ≤ DualSSD.Shared.secondPerformance P X η
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α) := by
  have h := tg_gap P X hX η hp
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
theorem tg_eq_at_cdf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) :
    DualSSD.Shared.distFun P X η ∈ Icc (0:ℝ) 1 ∧
    DualSSD.Shared.secondPerformance P X η
        + (∫ α in (0:ℝ)..(DualSSD.Shared.distFun P X η), DualSSD.MeanRisk.leftQuantile P X α)
      = DualSSD.Shared.distFun P X η * η := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hF : DualSSD.Shared.distFun P X η = cdf (P.map X) η := by
    rw [tg_distFun_eq P X hX.aemeasurable]
  have hp : DualSSD.Shared.distFun P X η ∈ Icc (0:ℝ) 1 := by
    rw [hF]; exact ⟨cdf_nonneg _ _, cdf_le_one _ _⟩
  refine ⟨hp, ?_⟩
  have h := tg_gap P X hX η hp
  have h0 : ∫ α, (max (η - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic (DualSSD.Shared.distFun P X η)).indicator
              (fun α => DualSSD.MeanRisk.leftQuantile P X α - η) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro α hα
    rw [tg_leftQuantile_eq P X hX.aemeasurable, hF]
    have hg := tg_Q_le_iff (P.map X) hα.1 hα.2 η
    by_cases hαp : α ∈ Iic (cdf (P.map X) η)
    · rw [indicator_of_mem hαp]
      have h1 : tgQ (P.map X) α ≤ η := hg.mpr hαp
      rw [max_eq_left (by linarith)]
      ring
    · rw [indicator_of_notMem hαp]
      have h1 : ¬ tgQ (P.map X) α ≤ η := fun h => hαp (hg.mp h)
      rw [max_eq_right (by linarith [not_le.mp h1])]
      ring
  linarith

open MeasureTheory ProbabilityTheory Set in
/-- Equality in Young at `η = F^(-1)(p)`, `0 < p < 1`. -/
theorem tg_eq_at_Q {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    DualSSD.Shared.secondPerformance P X (DualSSD.MeanRisk.leftQuantile P X p)
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α)
      = p * DualSSD.MeanRisk.leftQuantile P X p := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hpI : p ∈ Icc (0:ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have h := tg_gap P X hX (DualSSD.MeanRisk.leftQuantile P X p) hpI
  have h0 : ∫ α, (max (DualSSD.MeanRisk.leftQuantile P X p - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.MeanRisk.leftQuantile P X α
              - DualSSD.MeanRisk.leftQuantile P X p) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro α hα
    rw [tg_leftQuantile_eq P X hX.aemeasurable]
    have hm := tg_Q_mono (P.map X)
    by_cases hαp : α ∈ Iic p
    · rw [indicator_of_mem hαp]
      have h1 : tgQ (P.map X) α ≤ tgQ (P.map X) p := hm hα hp hαp
      rw [max_eq_left (by linarith)]
      ring
    · rw [indicator_of_notMem hαp]
      have h1 : tgQ (P.map X) p ≤ tgQ (P.map X) α :=
        hm hp hα (le_of_lt (not_le.mp hαp))
      rw [max_eq_right (by linarith)]
      ring
  linarith

open MeasureTheory ProbabilityTheory Set in
/-- The absolute Lorenz curve is continuous on `[0,1]`. -/
theorem tg_L_cont {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) :
    ContinuousOn (fun p => ∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α) (Icc 0 1) := by
  have hQ := tg_Q_int P X hX
  have h1 : IntegrableOn (DualSSD.MeanRisk.leftQuantile P X) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (integrableOn_Icc_iff_integrableOn_Ioo).mpr hQ
  have h2 := intervalIntegral.continuousOn_primitive_interval h1
  rwa [uIcc_of_le zero_le_one] at h2


open MeasureTheory ProbabilityTheory Set in
theorem tg_distFun_congr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f g : Ω → ℝ}
    (h : f =ᵐ[P] g) : DualSSD.Shared.distFun P f = DualSSD.Shared.distFun P g := by
  funext η
  simp only [DualSSD.Shared.distFun, measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [h] with ω hω
  change (f ω ≤ η) = (g ω ≤ η)
  rw [hω]

open MeasureTheory ProbabilityTheory Set in
theorem tg_tailGini_congr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f g : Ω → ℝ}
    (h : f =ᵐ[P] g) (p : ℝ) :
    DualSSD.MeanRisk.tailGini P f p = DualSSD.MeanRisk.tailGini P g p := by
  have hL : DualSSD.MeanRisk.leftQuantile P f = DualSSD.MeanRisk.leftQuantile P g := by
    funext α
    simp only [DualSSD.MeanRisk.leftQuantile, tg_distFun_congr P h]
  have hm : DualSSD.MeanRisk.mean P f = DualSSD.MeanRisk.mean P g := integral_congr_ae h
  simp only [DualSSD.MeanRisk.tailGini, DualSSD.MeanRisk.secondQuantileR, hL, hm]

open MeasureTheory ProbabilityTheory Set Pointwise in
theorem tg_Q_smul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) {c : ℝ}
    (hc : 0 < c) (α : ℝ) :
    DualSSD.MeanRisk.leftQuantile P (fun ω => c * X ω) α
      = c * DualSSD.MeanRisk.leftQuantile P X α := by
  have hset : {η : ℝ | α ≤ DualSSD.Shared.distFun P (fun ω => c * X ω) η}
      = c • {η : ℝ | α ≤ DualSSD.Shared.distFun P X η} := by
    ext η
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
    simp only [Set.mem_ofPred_eq, smul_eq_mul, DualSSD.Shared.distFun]
    have : {ω | c * X ω ≤ η} = {ω | X ω ≤ c⁻¹ * η} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [le_inv_mul_iff₀ hc]
    rw [this]
  rw [DualSSD.MeanRisk.leftQuantile, hset, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
  rfl

open MeasureTheory ProbabilityTheory Set in
theorem tg_tailGini_smul {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) {c : ℝ}
    (hc : 0 < c) (p : ℝ) :
    DualSSD.MeanRisk.tailGini P (fun ω => c * X ω) p = c * DualSSD.MeanRisk.tailGini P X p := by
  have hm : DualSSD.MeanRisk.mean P (fun ω => c * X ω) = c * DualSSD.MeanRisk.mean P X :=
    integral_const_mul c X
  have hS : ∀ α, DualSSD.MeanRisk.secondQuantileR P (fun ω => c * X ω) α
      = c * DualSSD.MeanRisk.secondQuantileR P X α := by
    intro α
    simp only [DualSSD.MeanRisk.secondQuantileR, tg_Q_smul P X hc]
    exact intervalIntegral.integral_const_mul c _
  simp only [DualSSD.MeanRisk.tailGini, hm, hS]
  have : ∀ α : ℝ, c * DualSSD.MeanRisk.mean P X * α - c * DualSSD.MeanRisk.secondQuantileR P X α
      = c * (DualSSD.MeanRisk.mean P X * α - DualSSD.MeanRisk.secondQuantileR P X α) := by
    intro α; ring
  simp only [this, intervalIntegral.integral_const_mul]
  ring

open MeasureTheory ProbabilityTheory Set in
/-- Concavity of the absolute Lorenz curve in the random variable, on `(0,1)`. -/
theorem tg_L_concave_Ioo {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (_hab : a + b = 1) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    a * (∫ β in (0:ℝ)..α, DualSSD.MeanRisk.leftQuantile P X β)
      + b * (∫ β in (0:ℝ)..α, DualSSD.MeanRisk.leftQuantile P Y β)
      ≤ ∫ β in (0:ℝ)..α, DualSSD.MeanRisk.leftQuantile P (fun ω => a * X ω + b * Y ω) β := by
  have hZ : Integrable (fun ω => a * X ω + b * Y ω) P := (hX.const_mul a).add (hY.const_mul b)
  have eX := tg_eq_at_Q P X hX hα
  have eY := tg_eq_at_Q P Y hY hα
  set qX := DualSSD.MeanRisk.leftQuantile P X α
  set qY := DualSSD.MeanRisk.leftQuantile P Y α
  have yZ := tg_young P (fun ω => a * X ω + b * Y ω) hZ (a * qX + b * qY) (p := α)
    ⟨hα.1.le, hα.2.le⟩
  rw [tg_perf_eq P X hX] at eX
  rw [tg_perf_eq P Y hY] at eY
  rw [tg_perf_eq P _ hZ] at yZ
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
theorem tg_g_cont {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) :
    ContinuousOn (fun α => DualSSD.MeanRisk.mean P X * α - DualSSD.MeanRisk.secondQuantileR P X α)
      (Icc 0 1) :=
  (continuousOn_const.mul continuousOn_id).sub (tg_L_cont P X hX)

open MeasureTheory ProbabilityTheory Set in
theorem tg_tailGini_convex {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) {p : ℝ} (hp : p ∈ Ioc (0 : ℝ) 1) :
    DualSSD.MeanRisk.tailGini P (fun ω => a * X ω + b * Y ω) p
      ≤ a * DualSSD.MeanRisk.tailGini P X p + b * DualSSD.MeanRisk.tailGini P Y p := by
  have hZ : Integrable (fun ω => a * X ω + b * Y ω) P := (hX.const_mul a).add (hY.const_mul b)
  have hm : DualSSD.MeanRisk.mean P (fun ω => a * X ω + b * Y ω)
      = a * DualSSD.MeanRisk.mean P X + b * DualSSD.MeanRisk.mean P Y := by
    simp only [DualSSD.MeanRisk.mean]
    rw [integral_add (hX.const_mul a) (hY.const_mul b), integral_const_mul, integral_const_mul]
  set gX := fun α => DualSSD.MeanRisk.mean P X * α - DualSSD.MeanRisk.secondQuantileR P X α
  set gY := fun α => DualSSD.MeanRisk.mean P Y * α - DualSSD.MeanRisk.secondQuantileR P Y α
  set gZ := fun α => DualSSD.MeanRisk.mean P (fun ω => a * X ω + b * Y ω) * α
    - DualSSD.MeanRisk.secondQuantileR P (fun ω => a * X ω + b * Y ω) α
  have cX : ContinuousOn gX (Icc 0 1) := tg_g_cont P X hX
  have cY : ContinuousOn gY (Icc 0 1) := tg_g_cont P Y hY
  have cZ : ContinuousOn gZ (Icc 0 1) := tg_g_cont P _ hZ
  have hcl : closure (Set.Ioo (0:ℝ) 1) = Set.Icc 0 1 := closure_Ioo zero_ne_one
  have key : ∀ α ∈ Icc (0:ℝ) 1, gZ α ≤ a * gX α + b * gY α := by
    have h1 : ∀ α ∈ Ioo (0:ℝ) 1, gZ α ≤ (fun α => a * gX α + b * gY α) α := by
      intro α hα
      have := tg_L_concave_Ioo P X Y hX hY ha hb hab hα
      simp only [gX, gY, gZ, hm, DualSSD.MeanRisk.secondQuantileR]
      nlinarith
    intro α hα
    refine le_on_closure h1 ?_ ?_ (by rw [hcl]; exact hα)
    · rw [hcl]; exact cZ
    · rw [hcl]; exact (continuousOn_const.mul cX).add (continuousOn_const.mul cY)
  have hsub : uIcc (0:ℝ) p ⊆ Icc 0 1 := by
    rw [uIcc_of_le hp.1.le]; exact Icc_subset_Icc_right hp.2
  have iX : IntervalIntegrable gX volume 0 p := (cX.mono hsub).intervalIntegrable
  have iY : IntervalIntegrable gY volume 0 p := (cY.mono hsub).intervalIntegrable
  have iZ : IntervalIntegrable gZ volume 0 p := (cZ.mono hsub).intervalIntegrable
  have hint : ∫ α in (0:ℝ)..p, gZ α ≤ ∫ α in (0:ℝ)..p, (a * gX α + b * gY α) := by
    apply intervalIntegral.integral_mono_on hp.1.le iZ ((iX.const_mul a).add (iY.const_mul b))
    intro α hα
    exact key α ⟨hα.1, le_trans hα.2 hp.2⟩
  rw [intervalIntegral.integral_add (iX.const_mul a) (iY.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  have hc : 0 ≤ 2 / p ^ 2 := by positivity
  show 2 / p ^ 2 * (∫ α in (0:ℝ)..p, gZ α)
      ≤ a * (2 / p ^ 2 * ∫ α in (0:ℝ)..p, gX α) + b * (2 / p ^ 2 * ∫ α in (0:ℝ)..p, gY α)
  have := mul_le_mul_of_nonneg_left hint hc
  linarith

open MeasureTheory DualSSD.MeanRisk in
theorem checked_tailGini_convex_posHomogeneous {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1) :
    ConvexOn ℝ Set.univ (fun X : Lp ℝ 1 P => tailGini P (⇑X) p) ∧
      ∀ c : ℝ, 0 < c → ∀ X : Lp ℝ 1 P, tailGini P ⇑(c • X) p = c * tailGini P (⇑X) p := by
  refine ⟨⟨convex_univ, ?_⟩, ?_⟩
  · intro x _ y _ a b ha hb hab
    have hae : (⇑(a • x + b • y) : Ω → ℝ) =ᵐ[P] fun ω => a * x ω + b * y ω := by
      filter_upwards [Lp.coeFn_add (a • x) (b • y), Lp.coeFn_smul a x, Lp.coeFn_smul b y]
        with ω h1 h2 h3
      rw [h1, Pi.add_apply, h2, h3]
      rfl
    show tailGini P (⇑(a • x + b • y)) p ≤ a • tailGini P (⇑x) p + b • tailGini P (⇑y) p
    rw [tg_tailGini_congr P hae, smul_eq_mul, smul_eq_mul]
    exact tg_tailGini_convex P x y (L1.integrable_coeFn x) (L1.integrable_coeFn y) ha hb hab hp
  · intro c hc X
    have hae : (⇑(c • X) : Ω → ℝ) =ᵐ[P] fun ω => c * X ω := by
      filter_upwards [Lp.coeFn_smul c X] with ω h1
      rw [h1]
      rfl
    rw [tg_tailGini_congr P hae]
    exact tg_tailGini_smul P X hc p

end GiniConvexity
end

section
namespace GiniDiameterConvexity
-- Prove2me | solution 1 for DualSSD.MeanRisk.hDiam_convex_posHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:28:30.631075+00:00
-- url     : https://prove2.me/submissions/1ccb54b0-8bfb-48e9-ae62-81eab40fb1bd


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
    simp only [Set.mem_ofPred_eq, smul_eq_mul, DualSSD.Shared.distFun]
    have : {ω | c * X ω ≤ η} = {ω | X ω ≤ c⁻¹ * η} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
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
    (_hab : a + b = 1) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
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
theorem checked_hDiam_convex_posHomogeneous {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
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
end GiniDiameterConvexity
end

section
namespace GiniDiameterMinimum
-- Prove2me | solution 1 for DualSSD.MeanRisk.hDiam_eq_min
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:49:29.967511+00:00
-- url     : https://prove2.me/submissions/2da00a12-0455-4df8-89d1-c589f4cefa0f


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
    DualSSD.MeanRisk.leftQuantile P X = dssdQ (P.map X) := by
  funext u
  rw [DualSSD.MeanRisk.leftQuantile, dssdQ, dssd_distFun_eq P X hX]

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
    Integrable (DualSSD.MeanRisk.leftQuantile P X) (volume.restrict (Ioo (0:ℝ) 1)) := by
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
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α) - p * η
      = ∫ α, (max (η - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.MeanRisk.leftQuantile P X α - η) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  set Q := DualSSD.MeanRisk.leftQuantile P X with hQdef
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
theorem dssd_Q_le_iff' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : AEMeasurable X P) {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) (x : ℝ) :
    DualSSD.MeanRisk.leftQuantile P X u ≤ x ↔ u ≤ DualSSD.Shared.distFun P X x := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  rw [dssd_leftQuantile_eq P X hX, dssd_distFun_eq P X hX]
  exact dssd_Q_le_iff (P.map X) hu.1 hu.2 x

open MeasureTheory ProbabilityTheory Set in
/-- Equality in Young at a `p`-quantile. -/
theorem dssd_eq_at_pq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (ξ : ℝ)
    (hξ : DualSSD.MeanRisk.IsPQuantile P X p ξ) :
    DualSSD.Shared.secondPerformance P X ξ
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α) = p * ξ := by
  have hpI : p ∈ Icc (0:ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have h := dssd_gap P X hX ξ hpI
  have h0 : ∫ α, (max (ξ - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.MeanRisk.leftQuantile P X α - ξ) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro α hα
    have hg := dssd_Q_le_iff' P X hX.aemeasurable hα
    by_cases hαp : α ∈ Iic p
    · rw [indicator_of_mem hαp]
      have h1 : DualSSD.MeanRisk.leftQuantile P X α ≤ ξ :=
        (hg ξ).mpr (le_trans (mem_Iic.mp hαp) hξ.2)
      rw [max_eq_left (by linarith)]
      ring
    · rw [indicator_of_notMem hαp]
      have hpa : p < α := not_le.mp hαp
      have h1 : ξ ≤ DualSSD.MeanRisk.leftQuantile P X α := by
        by_contra hlt
        have hlt' : DualSSD.MeanRisk.leftQuantile P X α < ξ := not_le.mp hlt
        have h2 : α ≤ DualSSD.Shared.distFun P X (DualSSD.MeanRisk.leftQuantile P X α) :=
          (hg _).mp le_rfl
        have h3 : DualSSD.Shared.distFun P X (DualSSD.MeanRisk.leftQuantile P X α)
            ≤ P.real {ω | X ω < ξ} := by
          unfold DualSSD.Shared.distFun
          exact measureReal_mono (fun ω hω => lt_of_le_of_lt hω hlt')
        linarith [hξ.1]
      rw [max_eq_right (by linarith)]
      ring
  linarith

open MeasureTheory ProbabilityTheory Set in
/-- Equality in Young at `η = F^(-1)(p)`, `0 < p < 1`. -/
theorem dssd_eq_at_Q {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    DualSSD.Shared.secondPerformance P X (DualSSD.MeanRisk.leftQuantile P X p)
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α)
      = p * DualSSD.MeanRisk.leftQuantile P X p := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hpI : p ∈ Icc (0:ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have h := dssd_gap P X hX (DualSSD.MeanRisk.leftQuantile P X p) hpI
  have h0 : ∫ α, (max (DualSSD.MeanRisk.leftQuantile P X p - DualSSD.MeanRisk.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.MeanRisk.leftQuantile P X α
              - DualSSD.MeanRisk.leftQuantile P X p) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro α hα
    rw [dssd_leftQuantile_eq P X hX.aemeasurable]
    have hm := dssd_Q_mono (P.map X)
    by_cases hαp : α ∈ Iic p
    · rw [indicator_of_mem hαp]
      have h1 : dssdQ (P.map X) α ≤ dssdQ (P.map X) p := hm hα hp hαp
      rw [max_eq_left (by linarith)]
      ring
    · rw [indicator_of_notMem hαp]
      have h1 : dssdQ (P.map X) p ≤ dssdQ (P.map X) α :=
        hm hp hα (le_of_lt (not_le.mp hαp))
      rw [max_eq_right (by linarith)]
      ring
  linarith

open MeasureTheory ProbabilityTheory Set in
/-- Young/Fenchel inequality: `p η ≤ F^(2)(η) + F^(-2)(p)`. -/
theorem dssd_young {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    p * η ≤ DualSSD.Shared.secondPerformance P X η
        + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α) := by
  have h := dssd_gap P X hX η hp
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

open MeasureTheory in
/-- The objective as `p (μ - ξ) + F^(2)(ξ)`. -/
theorem dssd_obj_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (ξ : ℝ) :
    ∫ ω, max (p * (X ω - ξ)) ((1 - p) * (ξ - X ω)) ∂P
      = DualSSD.MeanRisk.hDiam P X p
        + (DualSSD.Shared.secondPerformance P X ξ
          + (∫ α in (0:ℝ)..p, DualSSD.MeanRisk.leftQuantile P X α) - p * ξ) := by
  have hpt : ∀ ω, max (p * (X ω - ξ)) ((1 - p) * (ξ - X ω))
      = (p * X ω - p * ξ) + max (ξ - X ω) 0 := by
    intro ω
    have h0 := hp.1
    have h1 := hp.2
    rcases le_total (X ω) ξ with h | h
    · rw [max_eq_left (by linarith : (0:ℝ) ≤ ξ - X ω), max_eq_right (by nlinarith)]
      ring
    · rw [max_eq_right (by linarith : ξ - X ω ≤ 0), max_eq_left (by nlinarith)]
      ring
  have hi1 : Integrable (fun ω => p * X ω - p * ξ) P :=
    (hX.const_mul p).sub (integrable_const _)
  have hi2 : Integrable (fun ω => max (ξ - X ω) 0) P := ((integrable_const ξ).sub hX).pos_part
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hi1 hi2,
    integral_sub (hX.const_mul p) (integrable_const _), integral_const_mul,
    ← dssd_perf_eq P X hX ξ]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold DualSSD.MeanRisk.hDiam DualSSD.MeanRisk.mean DualSSD.MeanRisk.secondQuantileR
  ring

open MeasureTheory DualSSD.MeanRisk in
theorem checked_hDiam_eq_min {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    IsLeast (Set.range fun ξ : ℝ => ∫ ω, max (p * (X ω - ξ)) ((1 - p) * (ξ - X ω)) ∂P)
        (hDiam P X p) ∧
      ∀ ξ : ℝ, IsPQuantile P X p ξ →
        ∫ ω, max (p * (X ω - ξ)) ((1 - p) * (ξ - X ω)) ∂P = hDiam P X p := by
  have hpI : p ∈ Set.Icc (0:ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  refine ⟨⟨⟨leftQuantile P X p, ?_⟩, ?_⟩, ?_⟩
  · simp only
    rw [dssd_obj_eq P X hX hp, dssd_eq_at_Q P X hX hp]
    ring
  · rintro y ⟨ξ, rfl⟩
    simp only
    rw [dssd_obj_eq P X hX hp]
    linarith [dssd_young P X hX ξ hpI]
  · intro ξ hξ
    rw [dssd_obj_eq P X hX hp, dssd_eq_at_pq P X hX hp ξ hξ]
    ring
end GiniDiameterMinimum
end

section
namespace GiniQuantileDuality
-- Prove2me | solution 1 for DualSSD.Duality.ssd_iff_secondQuantile_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T10:07:13.644314+00:00
-- url     : https://prove2.me/submissions/24af3a16-a50a-4c61-a8f1-d10c467ef9d4


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

open MeasureTheory ProbabilityTheory Set in
/-- Equality in Young at `η = F^(-1)(p)`, `0 < p < 1`. -/
theorem dssd_eq_at_Q {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    DualSSD.Shared.secondPerformance P X (DualSSD.Duality.leftQuantile P X p)
        + (∫ α in (0:ℝ)..p, DualSSD.Duality.leftQuantile P X α)
      = p * DualSSD.Duality.leftQuantile P X p := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hpI : p ∈ Icc (0:ℝ) 1 := ⟨hp.1.le, hp.2.le⟩
  have h := dssd_gap P X hX (DualSSD.Duality.leftQuantile P X p) hpI
  have h0 : ∫ α, (max (DualSSD.Duality.leftQuantile P X p - DualSSD.Duality.leftQuantile P X α) 0
          + (Iic p).indicator (fun α => DualSSD.Duality.leftQuantile P X α
              - DualSSD.Duality.leftQuantile P X p) α)
          ∂(volume.restrict (Ioo (0:ℝ) 1)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro α hα
    rw [dssd_leftQuantile_eq P X hX.aemeasurable]
    have hm := dssd_Q_mono (P.map X)
    by_cases hαp : α ∈ Iic p
    · rw [indicator_of_mem hαp]
      have h1 : dssdQ (P.map X) α ≤ dssdQ (P.map X) p := hm hα hp hαp
      rw [max_eq_left (by linarith)]
      ring
    · rw [indicator_of_notMem hαp]
      have h1 : dssdQ (P.map X) p ≤ dssdQ (P.map X) α :=
        hm hp hα (le_of_lt (not_le.mp hαp))
      rw [max_eq_right (by linarith)]
      ring
  linarith

open MeasureTheory ProbabilityTheory Set in
/-- The absolute Lorenz curve is continuous on `[0,1]`. -/
theorem dssd_L_cont {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) :
    ContinuousOn (fun p => ∫ α in (0:ℝ)..p, DualSSD.Duality.leftQuantile P X α) (Icc 0 1) := by
  have hQ := dssd_Q_int P X hX
  have h1 : IntegrableOn (DualSSD.Duality.leftQuantile P X) (uIcc (0:ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (integrableOn_Icc_iff_integrableOn_Ioo).mpr hQ
  have h2 := intervalIntegral.continuousOn_primitive_interval h1
  rwa [uIcc_of_le zero_le_one] at h2

open MeasureTheory DualSSD DualSSD.Duality in
theorem checked_ssd_iff_secondQuantile_ge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P) :
    Shared.SSD P X Y ↔ ∀ p ∈ Set.Icc (0 : ℝ) 1, secondQuantile P Y p ≤ secondQuantile P X p := by
  have hsq : ∀ (Z : Ω → ℝ) (p : ℝ), p ∈ Set.Icc (0 : ℝ) 1 →
      secondQuantile P Z p = ((∫ α in (0:ℝ)..p, leftQuantile P Z α : ℝ) : EReal) := by
    intro Z p hp
    rw [secondQuantile, if_pos hp]
  constructor
  · intro h p hp
    rw [hsq Y p hp, hsq X p hp, EReal.coe_le_coe_iff]
    have key : ∀ q ∈ Set.Ioo (0 : ℝ) 1, (∫ α in (0:ℝ)..q, leftQuantile P Y α)
        ≤ ∫ α in (0:ℝ)..q, leftQuantile P X α := by
      intro q hq
      have e1 := dssd_eq_at_Q P Y hY hq
      have e2 := h (leftQuantile P Y q)
      have e3 := dssd_young P X hX (leftQuantile P Y q) (p := q) ⟨hq.1.le, hq.2.le⟩
      linarith
    have hcl : closure (Set.Ioo (0:ℝ) 1) = Set.Icc 0 1 := closure_Ioo zero_ne_one
    refine le_on_closure key ?_ ?_ (by rw [hcl]; exact hp)
    · rw [hcl]; exact dssd_L_cont P Y hY
    · rw [hcl]; exact dssd_L_cont P X hX
  · intro h η
    obtain ⟨hp, e1⟩ := dssd_eq_at_cdf P X hX η
    have e2 := h _ hp
    rw [hsq Y _ hp, hsq X _ hp, EReal.coe_le_coe_iff] at e2
    have e3 := dssd_young P Y hY η hp
    linarith
end GiniQuantileDuality
end

end

/- Complete checked body: LorenzLipschitz -/
section

open MeasureTheory Set
open DualSSD.MeanRisk

namespace DualSSD.MeanRiskProof

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem shortfall_le_l1 (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) (η : ℝ) :
    (∫ ω, max (η-X ω) 0 ∂P) ≤
      (∫ ω, max (η-Y ω) 0 ∂P) + ∫ ω, ‖X ω-Y ω‖ ∂P := by
  have hiX : Integrable (fun ω => max (η-X ω) 0) P := ((integrable_const η).sub hX).pos_part
  have hiY : Integrable (fun ω => max (η-Y ω) 0) P := ((integrable_const η).sub hY).pos_part
  have hiD : Integrable (fun ω => ‖X ω-Y ω‖) P := (hX.sub hY).norm
  rw [← integral_add hiY hiD]
  apply integral_mono hiX (hiY.add hiD)
  intro ω
  change max (η-X ω) 0 ≤ max (η-Y ω) 0 + ‖X ω-Y ω‖
  rw [Real.norm_eq_abs]
  apply max_le
  · have := le_max_left (η-Y ω) 0
    have := neg_abs_le (X ω-Y ω)
    linarith
  · exact add_nonneg (le_max_right _ _) (abs_nonneg _)

theorem lorenz_le_add_l1 (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P)
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    secondQuantileR P Y p ≤ secondQuantileR P X p + ∫ ω, ‖X ω-Y ω‖ ∂P := by
  have hinner : ∀ a ∈ Ioo (0 : ℝ) 1,
      secondQuantileR P Y a ≤ secondQuantileR P X a + ∫ ω, ‖X ω-Y ω‖ ∂P := by
    intro a ha
    have hxe := GiniConvexity.tg_young P X hX (leftQuantile P Y a)
      (p := a) ⟨ha.1.le,ha.2.le⟩
    have hye := GiniConvexity.tg_eq_at_Q P Y hY ha
    rw [GiniConvexity.tg_perf_eq P X hX] at hxe
    rw [GiniConvexity.tg_perf_eq P Y hY] at hye
    have hs := shortfall_le_l1 P X Y hX hY (leftQuantile P Y a)
    change secondQuantileR P Y a ≤ secondQuantileR P X a + _
    dsimp only [secondQuantileR]
    linarith
  have hcl : closure (Ioo (0 : ℝ) 1) = Icc 0 1 := closure_Ioo zero_ne_one
  apply le_on_closure hinner
  · rw [hcl]
    exact GiniConvexity.tg_L_cont P Y hY
  · rw [hcl]
    exact (GiniConvexity.tg_L_cont P X hX).add continuousOn_const
  · rwa [hcl]

omit [IsProbabilityMeasure P] in
theorem mean_le_add_l1 (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) :
    mean P Y ≤ mean P X + ∫ ω, ‖X ω-Y ω‖ ∂P := by
  have h := norm_integral_le_integral_norm (μ := P) (fun ω => Y ω-X ω)
  rw [integral_sub hY hX] at h
  simp only [norm_sub_rev (Y _) (X _)] at h
  rw [Real.norm_eq_abs] at h
  have hh := (le_abs_self (∫ ω, Y ω ∂P - ∫ ω, X ω ∂P)).trans h
  dsimp only [mean]
  linarith

noncomputable def objective (lam : ℝ) (X : Ω → ℝ) : ℝ := mean P X-lam*gini P X

theorem objective_eq (lam : ℝ) (X : Ω → ℝ) (hX : Integrable X P) :
    objective P lam X = (1-lam)*mean P X +
      2*lam*(∫ p in (0 : ℝ)..1, secondQuantileR P X p) := by
  have h := GiniConsistency.dssd_mg P X hX
  unfold objective
  nlinarith [congrArg (fun a : ℝ => lam*a) h]

theorem objective_le_add_l1 (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (X Y : Ω → ℝ) (hX : Integrable X P) (hY : Integrable Y P) :
    objective P lam Y ≤ objective P lam X + 2*(∫ ω, ‖X ω-Y ω‖ ∂P) := by
  let D := ∫ ω, ‖X ω-Y ω‖ ∂P
  have hD : 0 ≤ D := integral_nonneg (fun _ => norm_nonneg _)
  have hM := mean_le_add_l1 P X Y hX hY
  have hLX : IntervalIntegrable (secondQuantileR P X) volume 0 1 := (GiniConvexity.tg_L_cont P X hX).intervalIntegrable_of_Icc zero_le_one
  have hLY : IntervalIntegrable (secondQuantileR P Y) volume 0 1 := (GiniConvexity.tg_L_cont P Y hY).intervalIntegrable_of_Icc zero_le_one
  have hL : (∫ p in (0 : ℝ)..1, secondQuantileR P Y p) ≤
      (∫ p in (0 : ℝ)..1, secondQuantileR P X p) + D := by
    have h := intervalIntegral.integral_mono_on zero_le_one hLY
      (hLX.add (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => D) volume 0 1))
      (fun p hp => lorenz_le_add_l1 P X Y hX hY p hp)
    simpa only [intervalIntegral.integral_add hLX intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, one_smul] using h
  rw [objective_eq P lam X hX, objective_eq P lam Y hY]
  have h1 := mul_le_mul_of_nonneg_left hM (sub_nonneg.2 hlam1)
  have h2 := mul_le_mul_of_nonneg_left hL (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hlam0)
  change _ ≤ _ + 2*D
  nlinarith [mul_nonneg (sub_nonneg.2 hlam1) hD]

end DualSSD.MeanRiskProof

end

/- Complete checked body: ObjectiveLp -/
section

open MeasureTheory Set
open DualSSD.MeanRisk

namespace DualSSD.MeanRiskProof

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
variable (q : ENNReal) [Fact (1 ≤ q)]

theorem lp_integrable (X : Lp ℝ q P) : Integrable X P :=
  MemLp.integrable (Fact.out : 1 ≤ q) (Lp.memLp X)

theorem lp_l1_le_norm (X : Lp ℝ q P) : (∫ ω, ‖X ω‖ ∂P) ≤ ‖X‖ := by
  rw [Lp.norm_def, ← lpNorm_one_eq_integral_norm (Lp.aestronglyMeasurable X),
    ← toReal_eLpNorm (Lp.aestronglyMeasurable X)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top X)
    (eLpNorm_le_eLpNorm_of_exponent_le (Fact.out : 1 ≤ q) (Lp.aestronglyMeasurable X))

theorem lp_l1_diff_le_norm (X Y : Lp ℝ q P) :
    (∫ ω, ‖X ω-Y ω‖ ∂P) ≤ ‖X-Y‖ := by
  have he : (∫ ω, ‖X ω-Y ω‖ ∂P) = ∫ ω, ‖(X-Y) ω‖ ∂P := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub X Y] with ω hω
    rw [hω]
    rfl
  rw [he]
  exact lp_l1_le_norm P q (X-Y)

theorem objective_lipschitz (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    LipschitzWith 2 (fun X : Lp ℝ q P => objective P lam X) := by
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  have hXY := objective_le_add_l1 P lam h0 h1 X Y (lp_integrable P q X) (lp_integrable P q Y)
  have hYX := objective_le_add_l1 P lam h0 h1 Y X (lp_integrable P q Y) (lp_integrable P q X)
  have hb := lp_l1_diff_le_norm P q X Y
  have hb' := lp_l1_diff_le_norm P q Y X
  rw [norm_sub_rev Y X] at hb'
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

omit [IsProbabilityMeasure P] in
theorem objective_congr {X Y : Ω → ℝ} (h : X =ᵐ[P] Y) (lam : ℝ) :
    objective P lam X = objective P lam Y := by
  have hm : mean P X = mean P Y := integral_congr_ae h
  have hg := GiniConvexity.tg_tailGini_congr P h 1
  rw [← gini_eq_tailGini_one, ← gini_eq_tailGini_one] at hg
  simp only [objective, hm, hg]

theorem objective_concave (lam : ℝ) (h0 : 0 ≤ lam) :
    ConcaveOn ℝ univ (fun X : Lp ℝ q P => objective P lam X) := by
  refine ⟨convex_univ, ?_⟩
  intro X _ Y _ a b ha hb hab
  have hX := lp_integrable P q X
  have hY := lp_integrable P q Y
  have hae : (⇑(a • X+b • Y) : Ω → ℝ) =ᵐ[P] (fun ω => a*X ω+b*Y ω) := by
    filter_upwards [Lp.coeFn_add (a • X) (b • Y), Lp.coeFn_smul a X, Lp.coeFn_smul b Y]
      with ω hA hX hY
    rw [hA, Pi.add_apply, hX, hY]
    rfl
  change a*objective P lam X+b*objective P lam Y ≤ objective P lam (⇑(a • X+b • Y : Lp ℝ q P) : Ω → ℝ)
  rw [objective_congr P hae lam]
  have hmean : mean P (fun ω => a*X ω+b*Y ω) = a*mean P X+b*mean P Y := by
    simp only [mean, integral_add (hX.const_mul a) (hY.const_mul b), integral_const_mul]
  have hg := GiniConvexity.tg_tailGini_convex P X Y hX hY ha hb hab
    (p := 1) ⟨zero_lt_one,le_rfl⟩
  simp only [← gini_eq_tailGini_one] at hg
  have hh := mul_le_mul_of_nonneg_left hg h0
  simp only [objective, hmean]
  nlinarith

theorem objective_strict_ssd (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (X Y : Lp ℝ q P) (h : StrictSSD P Y X) : objective P lam X < objective P lam Y := by
  have hX := lp_integrable P q X
  have hY := lp_integrable P q Y
  have hmean := checked_mean_le_of_ssd P Y X hY hX h.1
  have hmg := (GiniConsistency.checked_meanGini_ssd_consistent P Y X hY hX).2 h
  have hstrict := mul_lt_mul_of_pos_left hmg h0
  have hweak := mul_le_mul_of_nonneg_left hmean (sub_nonneg.2 h1)
  unfold objective
  nlinarith

end DualSSD.MeanRiskProof

end

/- Complete checked body: MidpointMinimization -/
section

open Filter Topology Set

namespace DualSSD.MeanRiskProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Small midpoint deficit forces bounded pairs to be close. -/
def MidpointControl (F : E → ℝ) : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε → ∃ δ > 0,
    ∀ u v : E, ‖u‖ ≤ M → ‖v‖ ≤ M →
      F u + F v - 2 * F (midpoint ℝ u v) < δ → ‖u - v‖ < ε

theorem minimizing_cauchy {F : E → ℝ} (hF : MidpointControl F)
    {C : Set E} (hC : Convex ℝ C) {a M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ u ∈ C, ‖u‖ ≤ M) (hlower : ∀ u ∈ C, a ≤ F u)
    (u : ℕ → E) (hu : ∀ n, u n ∈ C)
    (hlim : Tendsto (fun n => F (u n)) atTop (𝓝 a)) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδ, hcontrol⟩ := hF M hM ε hε
  have he : ∀ᶠ n in atTop, F (u n) < a + δ / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  refine ⟨N, fun i hi j hj => ?_⟩
  have hm := hlower _ (hC.midpoint_mem (hu i) (hu j))
  have hsmall : F (u i) + F (u j) - 2 * F (midpoint ℝ (u i) (u j)) < δ := by
    have := hN i hi
    have := hN j hj
    linarith
  simpa only [dist_eq_norm] using hcontrol (u i) (u j)
    (hbound _ (hu i)) (hbound _ (hu j)) hsmall

theorem exists_minimizer_of_midpoint [CompleteSpace E] {F : E → ℝ}
    (hF : Continuous F) (hcontrol : MidpointControl F)
    {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ u ∈ C, ‖u‖ ≤ M)
    (hlower : BddBelow (F '' C)) : ∃ q ∈ C, ∀ u ∈ C, F q ≤ F u := by
  classical
  obtain ⟨a, _ha, halim, haC⟩ := exists_seq_tendsto_sInf (hne.image F) hlower
  have hex : ∀ n, ∃ u ∈ C, F u = a n := fun n => haC n
  choose u hu hua using hex
  have hulim : Tendsto (fun n => F (u n)) atTop (𝓝 (sInf (F '' C))) := by
    simpa only [hua] using halim
  have hmin : ∀ x ∈ C, sInf (F '' C) ≤ F x :=
    fun x hx => csInf_le hlower ⟨x, hx, rfl⟩
  have huc := minimizing_cauchy hcontrol hconv hM hbound hmin u hu hulim
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete huc
  have hqC : q ∈ C := hclosed.mem_of_tendsto hq (Eventually.of_forall hu)
  have hval : F q = sInf (F '' C) := tendsto_nhds_unique (hF.tendsto q |>.comp hq) hulim
  refine ⟨q, hqC, fun x hx => ?_⟩
  rw [hval]
  exact hmin x hx

theorem nested_minimizers_cauchy {F : E → ℝ} (hcontrol : MidpointControl F)
    (C : ℕ → Set E) (hconv : ∀ n, Convex ℝ (C n)) (hnest : Antitone C)
    (q : ℕ → E) (hq : ∀ n, q n ∈ C n)
    (hmin : ∀ n u, u ∈ C n → F (q n) ≤ F u)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ n, ‖q n‖ ≤ M)
    (hbdd : BddAbove (range (fun n => F (q n)))) : CauchySeq q := by
  have hmono : Monotone (fun n => F (q n)) := by
    intro i j hij
    exact hmin i (q j) (hnest hij (hq j))
  have hlim := tendsto_atTop_ciSup hmono hbdd
  have hreal := Metric.cauchySeq_iff.1 hlim.cauchySeq
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := hcontrol M hM ε hε
  obtain ⟨N, hN⟩ := hreal δ hδ
  refine ⟨N, fun i hi j hj => ?_⟩
  have hdefect : F (q i) + F (q j) - 2 * F (midpoint ℝ (q i) (q j)) < δ := by
    rcases le_total i j with hij | hji
    · have hmid := hmin i _ (hconv i |>.midpoint_mem (hq i) (hnest hij (hq j)))
      have hd := hN j hj i hi
      rw [Real.dist_eq] at hd
      have := (abs_lt.1 hd).2
      linarith
    · have hmid := hmin j _ (hconv j |>.midpoint_mem (hnest hji (hq i)) (hq j))
      have hd := hN i hi j hj
      rw [Real.dist_eq] at hd
      have := (abs_lt.1 hd).2
      linarith
  simpa only [dist_eq_norm] using hc (q i) (q j) (hbound i) (hbound j) hdefect

theorem nested_minimizers_limit [CompleteSpace E] {F : E → ℝ}
    (hcontrol : MidpointControl F) (C : ℕ → Set E)
    (hclosed : ∀ n, IsClosed (C n)) (hconv : ∀ n, Convex ℝ (C n))
    (hnest : Antitone C) (q : ℕ → E) (hq : ∀ n, q n ∈ C n)
    (hmin : ∀ n u, u ∈ C n → F (q n) ≤ F u)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ n, ‖q n‖ ≤ M)
    (hbdd : BddAbove (range (fun n => F (q n)))) :
    ∃ z, Tendsto q atTop (𝓝 z) ∧ ∀ n, z ∈ C n := by
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete
    (nested_minimizers_cauchy hcontrol C hconv hnest q hq hmin hM hbound hbdd)
  refine ⟨z, hz, fun n => ?_⟩
  exact (hclosed n).mem_of_tendsto hz
    (eventually_atTop.2 ⟨n, fun k hk => hnest hk (hq k)⟩)

end DualSSD.MeanRiskProof

end

/- Complete checked body: NestedAttainment -/
section

open Filter Topology Set

namespace DualSSD.MeanRiskProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_max_of_midpoint_control {F f : E → ℝ}
    (hF : Continuous F) (hc : MidpointControl F) (hF0 : ∀ u, 0 ≤ F u)
    {Q : Set E} (hQ : Q.Nonempty) (hclosed : IsClosed Q)
    (hf : Continuous f) (hconc : ConcaveOn ℝ Q f)
    {M B : ℝ} (hM : 0 ≤ M) (hbound : ∀ u ∈ Q, ‖u‖ ≤ M)
    (hFbound : ∀ u ∈ Q, F u ≤ B) (hfbdd : BddAbove (f '' Q)) :
    ∃ z ∈ Q, ∀ u ∈ Q, f u ≤ f z := by
  classical
  obtain ⟨a, ha, halim, haQ⟩ := exists_seq_tendsto_sSup (hQ.image f) hfbdd
  let C : ℕ → Set E := fun n => {u ∈ Q | a n ≤ f u}
  have hCne : ∀ n, (C n).Nonempty := by
    intro n
    obtain ⟨u, hu, he⟩ := haQ n
    exact ⟨u, hu, he.ge⟩
  have hCc : ∀ n, IsClosed (C n) := fun n => hclosed.inter (isClosed_le continuous_const hf)
  have hCv : ∀ n, Convex ℝ (C n) := fun n => hconc.convex_ge (a n)
  have hCn : Antitone C := by
    intro i j hij u hu
    exact ⟨hu.1, (ha hij).trans hu.2⟩
  have hex : ∀ n, ∃ q ∈ C n, ∀ u ∈ C n, F q ≤ F u := by
    intro n
    exact exists_minimizer_of_midpoint hF hc (hCne n) (hCc n) (hCv n)
      hM (fun u hu => hbound u hu.1)
      ⟨0, by rintro _ ⟨u,_hu,rfl⟩; exact hF0 u⟩
  choose q hq hmin using hex
  have hbdd : BddAbove (range (fun n => F (q n))) :=
    ⟨B, by rintro _ ⟨n,rfl⟩; exact hFbound (q n) (hq n).1⟩
  obtain ⟨z, _hz, hzC⟩ := nested_minimizers_limit hc C hCc hCv hCn q hq hmin
    hM (fun n => hbound (q n) (hq n).1) hbdd
  have hs : sSup (f '' Q) ≤ f z :=
    le_of_tendsto halim (Eventually.of_forall (fun n => (hzC n).2))
  exact ⟨z, (hzC 0).1, fun u hu => (le_csSup hfbdd ⟨u,hu,rfl⟩).trans hs⟩

end DualSSD.MeanRiskProof

end

/- Complete checked body: ScalarPower -/
section

open Set

namespace DualSSD.MeanRiskProof

noncomputable def scalarPower (p a : ℝ) : ℝ := |a| ^ p

noncomputable def scalarDefect (p a b : ℝ) : ℝ :=
  scalarPower p a + scalarPower p b - 2 * scalarPower p ((a+b)/2)

theorem scalarPower_nonneg (p a : ℝ) : 0 ≤ scalarPower p a :=
  Real.rpow_nonneg (abs_nonneg _) _

theorem scalarPower_continuous {p : ℝ} (hp : 0 < p) : Continuous (scalarPower p) := by
  exact continuous_abs.rpow_const (fun _ => Or.inr hp.le)

theorem scalarDefect_continuous {p : ℝ} (hp : 0 < p) :
    Continuous (fun z : ℝ × ℝ => scalarDefect p z.1 z.2) := by
  unfold scalarDefect
  exact ((scalarPower_continuous hp).comp continuous_fst |>.add
    ((scalarPower_continuous hp).comp continuous_snd)).sub
      (((scalarPower_continuous hp).comp
        ((continuous_fst.add continuous_snd).div_const 2)).const_mul 2)

theorem scalarPower_mul {p c : ℝ} (hc : 0 ≤ c) (a : ℝ) :
    scalarPower p (c*a) = c^p * scalarPower p a := by
  unfold scalarPower
  rw [abs_mul, abs_of_nonneg hc, Real.mul_rpow hc (abs_nonneg a)]

theorem scalarDefect_mul {p c : ℝ} (hc : 0 ≤ c) (a b : ℝ) :
    scalarDefect p (c*a) (c*b) = c^p * scalarDefect p a b := by
  have he : (c*a+c*b)/2 = c*((a+b)/2) := by ring
  unfold scalarDefect
  rw [he, scalarPower_mul hc, scalarPower_mul hc, scalarPower_mul hc]
  ring

theorem scalarDefect_nonneg {p : ℝ} (hp : 1 < p) (a b : ℝ) :
    0 ≤ scalarDefect p a b := by
  have ht : |(a+b)/2| ≤ (|a|+|b|)/2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right (abs_add_le a b) (by norm_num)
  have hpow := Real.rpow_le_rpow (abs_nonneg _) ht (by linarith : 0 ≤ p)
  have hc := (convexOn_rpow hp.le).2 (show |a| ∈ Ici (0:ℝ) from abs_nonneg a)
    (show |b| ∈ Ici (0:ℝ) from abs_nonneg b)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ)+1/2=1 by norm_num)
  simp only [smul_eq_mul] at hc
  have he : (1/2:ℝ)*|a|+(1/2)*|b| = (|a|+|b|)/2 := by ring
  rw [he] at hc
  unfold scalarDefect scalarPower
  linarith

theorem scalarDefect_pos {p : ℝ} (hp : 1 < p) {a b : ℝ} (hab : a ≠ b) :
    0 < scalarDefect p a b := by
  have hp0 : 0 < p := by linarith
  by_cases heq : |a| = |b|
  · have hneg : a = -b := (abs_eq_abs.mp heq).resolve_left hab
    have hzero : a+b=0 := by linarith
    have ha : a ≠ 0 := by
      intro ha
      have hb : b=0 := by simpa only [ha, abs_zero, eq_comm, abs_eq_zero] using heq
      exact hab (ha.trans hb.symm)
    have hpa : 0 < scalarPower p a := Real.rpow_pos_of_pos (abs_pos.mpr ha) p
    have hpb := scalarPower_nonneg p b
    unfold scalarDefect
    have hm : scalarPower p ((a+b)/2)=0 := by
      simp only [hzero, zero_div, scalarPower, abs_zero, Real.zero_rpow hp0.ne']
    rw [hm]
    linarith
  · have ht : |(a+b)/2| ≤ (|a|+|b|)/2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact div_le_div_of_nonneg_right (abs_add_le a b) (by norm_num)
    have hpow := Real.rpow_le_rpow (abs_nonneg _) ht hp0.le
    have hc := (strictConvexOn_rpow hp).2
      (show |a| ∈ Ici (0:ℝ) from abs_nonneg a)
      (show |b| ∈ Ici (0:ℝ) from abs_nonneg b) heq
      (show (0:ℝ)<1/2 by norm_num) (show (0:ℝ)<1/2 by norm_num)
      (show (1/2:ℝ)+1/2=1 by norm_num)
    simp only [smul_eq_mul] at hc
    have he : (1/2:ℝ)*|a|+(1/2)*|b| = (|a|+|b|)/2 := by ring
    rw [he] at hc
    unfold scalarDefect scalarPower
    linarith

end DualSSD.MeanRiskProof

end

/- Complete checked body: ScalarCompactness -/
section

open Set

namespace DualSSD.MeanRiskProof

theorem normalized_scalar_bound {p κ : ℝ} (hp : 1 < p) (hκ : 0 < κ) :
    ∃ C ≥ 0, ∀ a b : ℝ, max |a| |b| = 1 →
      scalarPower p (a-b) ≤ κ * (scalarPower p a + scalarPower p b) +
        C * scalarDefect p a b := by
  have hp0 : 0 < p := by linarith
  let K : Set (ℝ × ℝ) := {z | max |z.1| |z.2| = 1 ∧
    κ * (scalarPower p z.1 + scalarPower p z.2) ≤ scalarPower p (z.1-z.2)}
  have hc : IsClosed K := by
    apply IsClosed.inter
    · exact isClosed_eq (continuous_fst.abs.max continuous_snd.abs) continuous_const
    · exact isClosed_le (((scalarPower_continuous hp0).comp continuous_fst |>.add
        ((scalarPower_continuous hp0).comp continuous_snd)).const_mul κ)
        ((scalarPower_continuous hp0).comp (continuous_fst.sub continuous_snd))
  have hk : IsCompact K := by
    apply (isCompact_Icc : IsCompact (Icc ((-1:ℝ),(-1:ℝ)) (1,1))).of_isClosed_subset hc
    intro z hz
    have ha : |z.1| ≤ 1 := (le_max_left _ _).trans_eq hz.1
    have hb : |z.2| ≤ 1 := (le_max_right _ _).trans_eq hz.1
    exact ⟨⟨(abs_le.1 ha).1, (abs_le.1 hb).1⟩, ⟨(abs_le.1 ha).2, (abs_le.1 hb).2⟩⟩
  have hpos : ∀ z ∈ K, 0 < scalarDefect p z.1 z.2 := by
    intro z hz
    apply scalarDefect_pos hp
    intro he
    have hnorm : |z.2| = 1 := by simpa only [he, max_self] using hz.1
    have hbad := hz.2
    simp only [he, sub_self, scalarPower, abs_zero, Real.zero_rpow hp0.ne',
      hnorm, Real.one_rpow] at hbad
    linarith
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hk.exists_isMinOn hne (scalarDefect_continuous hp0).continuousOn
    let δ := scalarDefect p z.1 z.2
    have hδ : 0 < δ := hpos z hz
    let C := (2:ℝ)^p / δ
    have hC : 0 ≤ C := div_nonneg (Real.rpow_nonneg (by norm_num) _) hδ.le
    refine ⟨C, hC, fun a b hab => ?_⟩
    by_cases hbad : κ * (scalarPower p a + scalarPower p b) ≤ scalarPower p (a-b)
    · have hm : δ ≤ scalarDefect p a b := (isMinOn_iff.mp hmin) (a,b) ⟨hab,hbad⟩
      have habs : |a-b| ≤ 2 := by
        have ha := (le_max_left |a| |b|).trans_eq hab
        have hb := (le_max_right |a| |b|).trans_eq hab
        have hh : |a-b| ≤ |a|+|b| := by simpa only [Real.norm_eq_abs] using norm_sub_le a b
        linarith
      have hpow : scalarPower p (a-b) ≤ (2:ℝ)^p :=
        Real.rpow_le_rpow (abs_nonneg _) habs hp0.le
      have hmul := mul_le_mul_of_nonneg_left hm hC
      have he : C*δ=(2:ℝ)^p := by dsimp [C]; field_simp
      rw [he] at hmul
      have hn : 0 ≤ κ * (scalarPower p a + scalarPower p b) :=
        mul_nonneg hκ.le (add_nonneg (scalarPower_nonneg _ _) (scalarPower_nonneg _ _))
      linarith
    · have hd : 0 ≤ C * scalarDefect p a b := mul_nonneg hC (scalarDefect_nonneg hp a b)
      exact (lt_of_not_ge hbad).le.trans (le_add_of_nonneg_right hd)
  · refine ⟨0, le_rfl, fun a b hab => ?_⟩
    have hbad : ¬ κ * (scalarPower p a + scalarPower p b) ≤ scalarPower p (a-b) := by
      intro hh
      exact hne ⟨⟨a,b⟩, hab, hh⟩
    simpa only [zero_mul, add_zero] using (lt_of_not_ge hbad).le

theorem scalar_compactness_bound {p κ : ℝ} (hp : 1 < p) (hκ : 0 < κ) :
    ∃ C ≥ 0, ∀ a b : ℝ,
      scalarPower p (a-b) ≤ κ * (scalarPower p a + scalarPower p b) +
        C * scalarDefect p a b := by
  obtain ⟨C, hC, hc⟩ := normalized_scalar_bound hp hκ
  refine ⟨C, hC, fun a b => ?_⟩
  let r := max |a| |b|
  have hr0 : 0 ≤ r := (abs_nonneg a).trans (le_max_left _ _)
  by_cases hr : r=0
  · have ha : a=0 := abs_eq_zero.mp (le_antisymm (by simpa only [r, hr] using le_max_left |a| |b|) (abs_nonneg a))
    have hb : b=0 := abs_eq_zero.mp (le_antisymm (by simpa only [r, hr] using le_max_right |a| |b|) (abs_nonneg b))
    subst a b
    have hp0 : p≠0 := by linarith
    simp only [sub_self, scalarPower, scalarDefect, abs_zero, zero_add, zero_div,
      Real.zero_rpow hp0, mul_zero]
    exact le_rfl
  · have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    let u := a/r
    let v := b/r
    have hnormal : max |u| |v| = 1 := by
      dsimp [u,v]
      rw [abs_div, abs_div, abs_of_pos hrp, max_div_div_right hrp.le]
      exact div_self hr
    have ha : r*u=a := by dsimp [u]; field_simp
    have hb : r*v=b := by dsimp [v]; field_simp
    have hd : r*(u-v)=a-b := by rw [mul_sub, ha, hb]
    have h := mul_le_mul_of_nonneg_left (hc u v hnormal) (Real.rpow_nonneg hrp.le p)
    have hA := scalarPower_mul (p:=p) hrp.le u
    have hB := scalarPower_mul (p:=p) hrp.le v
    have hD := scalarPower_mul (p:=p) hrp.le (u-v)
    have hF := scalarDefect_mul (p:=p) hrp.le u v
    rw [ha] at hA
    rw [hb] at hB
    rw [hd] at hD
    rw [ha,hb] at hF
    calc
      scalarPower p (a-b) = r^p * scalarPower p (u-v) := hD
      _ ≤ r^p * (κ * (scalarPower p u + scalarPower p v) + C * scalarDefect p u v) := h
      _ = κ * (scalarPower p a + scalarPower p b) + C * scalarDefect p a b := by
        rw [hA, hB, hF]
        ring

end DualSSD.MeanRiskProof

end

/- Complete checked body: LpPowerIntegral -/
section

open MeasureTheory Set

namespace DualSSD.MeanRiskProof

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {q : ENNReal} [Fact (1 ≤ q)]

omit [Fact (1 ≤ q)] in
theorem lp_power_integrable (hq : 1 < q) (hqt : q ≠ ⊤) (X : Lp ℝ q P) :
    Integrable (fun ω => scalarPower q.toReal (X ω)) P := by
  simpa only [scalarPower, Real.norm_eq_abs] using
    memLp_one_iff_integrable.mp ((Lp.memLp X).norm_rpow (ne_of_gt (lt_trans zero_lt_one hq)) hqt)

omit [Fact (1 ≤ q)] in
theorem lp_integral_power (hq : 1 < q) (hqt : q ≠ ⊤) (X : Lp ℝ q P) :
    (∫ ω, scalarPower q.toReal (X ω) ∂P) = ‖X‖ ^ q.toReal := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hqt
  have hI : 0 ≤ ∫ ω, ‖X ω‖ ^ q.toReal ∂P :=
    integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg _) _)
  have hn : ‖X‖ = (∫ ω, ‖X ω‖ ^ q.toReal ∂P) ^ q.toReal⁻¹ := by
    rw [Lp.norm_def, (Lp.memLp X).eLpNorm_eq_integral_rpow_norm hq0 hqt,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)]
  rw [hn, ← Real.rpow_mul hI, inv_mul_cancel₀ hp.ne', Real.rpow_one]
  simp only [scalarPower, Real.norm_eq_abs]

theorem lp_scalar_bound (hq : 1 < q) (hqt : q ≠ ⊤) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C ≥ 0, ∀ X Y : Lp ℝ q P,
      ‖X-Y‖ ^ q.toReal ≤ κ * (‖X‖ ^ q.toReal + ‖Y‖ ^ q.toReal) +
        C * (‖X‖ ^ q.toReal + ‖Y‖ ^ q.toReal - 2 * ‖midpoint ℝ X Y‖ ^ q.toReal) := by
  have hp : 1 < q.toReal := by
    have h := ENNReal.toReal_lt_toReal (by norm_num : (1:ENNReal)≠⊤) hqt
    simpa only [ENNReal.toReal_one] using h.mpr hq
  obtain ⟨C, hC, hc⟩ := scalar_compactness_bound hp hκ
  refine ⟨C, hC, fun X Y => ?_⟩
  let Z := midpoint ℝ X Y
  have hZ : (fun ω => Z ω) =ᵐ[P] (fun ω => (X ω+Y ω)/2) := by
    dsimp [Z]
    rw [midpoint_eq_smul_add, invOf_eq_inv, ← one_div]
    filter_upwards [Lp.coeFn_smul (1/2:ℝ) (X+Y), Lp.coeFn_add X Y] with ω hω hxy
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at hω hxy
    rw [hω,hxy]
    ring
  have hD : (fun ω => (X-Y) ω) =ᵐ[P] (fun ω => X ω-Y ω) := Lp.coeFn_sub X Y
  have hX := lp_power_integrable hq hqt X
  have hY := lp_power_integrable hq hqt Y
  have hZi := lp_power_integrable hq hqt Z
  have hDi := lp_power_integrable hq hqt (X-Y)
  have he : ∀ᵐ ω ∂P, scalarPower q.toReal ((X-Y) ω) ≤
      κ * (scalarPower q.toReal (X ω) + scalarPower q.toReal (Y ω)) +
        C * (scalarPower q.toReal (X ω) + scalarPower q.toReal (Y ω) -
          2 * scalarPower q.toReal (Z ω)) := by
    filter_upwards [hZ,hD] with ω hz hd
    rw [hz,hd]
    exact hc (X ω) (Y ω)
  have hsum : Integrable (fun ω => scalarPower q.toReal (X ω) + scalarPower q.toReal (Y ω)) P := hX.add hY
  have hrest : Integrable (fun ω => scalarPower q.toReal (X ω) + scalarPower q.toReal (Y ω) -
      2 * scalarPower q.toReal (Z ω)) P := hsum.sub (hZi.const_mul 2)
  have hi := integral_mono_ae hDi ((hsum.const_mul κ).add (hrest.const_mul C)) he
  simp only [Pi.add_apply] at hi
  rw [integral_add (hsum.const_mul κ) (hrest.const_mul C),
    integral_const_mul, integral_const_mul, integral_sub hsum (hZi.const_mul 2),
    integral_add hX hY, integral_const_mul,
    lp_integral_power hq hqt (X-Y), lp_integral_power hq hqt X,
    lp_integral_power hq hqt Y, lp_integral_power hq hqt Z] at hi
  exact hi

end DualSSD.MeanRiskProof

end

/- Complete checked body: LpMidpoint -/
section

open MeasureTheory

namespace DualSSD.MeanRiskProof

theorem lp_midpoint_control {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (q : ENNReal) [Fact (1 ≤ q)] (hq : 1 < q) (hqt : q ≠ ⊤) :
    MidpointControl (fun X : Lp ℝ q P => ‖X‖ ^ q.toReal) := by
  have hp : 1 < q.toReal := by
    have h := ENNReal.toReal_lt_toReal (by norm_num : (1:ENNReal)≠⊤) hqt
    simpa only [ENNReal.toReal_one] using h.mpr hq
  have hp0 : 0 < q.toReal := by linarith
  intro M hM ε hε
  let e := ε ^ q.toReal
  have he : 0 < e := Real.rpow_pos_of_pos hε _
  let W := M ^ q.toReal
  have hW : 0 ≤ W := Real.rpow_nonneg hM _
  let κ := e / (4 * (W+1))
  have hκ : 0 < κ := div_pos he (by positivity)
  obtain ⟨C, hC, hc⟩ := lp_scalar_bound (P:=P) hq hqt κ hκ
  let δ := e / (2 * (C+1))
  have hδ : 0 < δ := div_pos he (by positivity)
  refine ⟨δ, hδ, fun X Y hX hY hdef => ?_⟩
  have hXp : ‖X‖ ^ q.toReal ≤ W := Real.rpow_le_rpow (norm_nonneg _) hX hp0.le
  have hYp : ‖Y‖ ^ q.toReal ≤ W := Real.rpow_le_rpow (norm_nonneg _) hY hp0.le
  have hkId : κ * (4*(W+1)) = e := by dsimp [κ]; field_simp
  have hdId : δ * (2*(C+1)) = e := by dsimp [δ]; field_simp
  have hfirst := mul_le_mul_of_nonneg_left (add_le_add hXp hYp) hκ.le
  have hsecond := mul_le_mul_of_nonneg_left hdef.le hC
  have hmain := hc X Y
  have hpow : ‖X-Y‖ ^ q.toReal < ε ^ q.toReal := by
    change ‖X-Y‖ ^ q.toReal < e
    nlinarith
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hp0).mp hpow

end DualSSD.MeanRiskProof

end

/- Complete checked body: MeanGiniRoot -/
section

namespace DualSSD.MeanRisk

open MeasureTheory

/-- **Theorem 5.3** (Ogryczak–Ruszczyński 2002, p. 73). Let `Q ⊆ L_q(Ω, P)`, `1 < q < ∞`, be
convex, bounded, closed and nonempty, and let `lam ∈ (0, 1]` (the paper's `λ`; `λ` is a Lean
keyword). Then the mean–Gini problem (5.1) `max_{X ∈ Q} (μ_X − lam Γ_X)` has an optimal solution
in `Q`, and every optimal solution is SSD-efficient in `Q` (no `Y ∈ Q` with `Y ≻_SSD X`).
`Q.Nonempty` is not on the page: the paper assumes it silently, and without it no optimal
solution exists. -/
theorem meanGini_optimal_exists_ssdEfficient {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (q : ENNReal) [Fact (1 ≤ q)] (hq : 1 < q) (hqtop : q ≠ ⊤)
    (Q : Set (Lp ℝ q P)) (hQconv : Convex ℝ Q) (hQbdd : Bornology.IsBounded Q)
    (hQclosed : IsClosed Q) (hQne : Q.Nonempty) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (∃ X ∈ Q, ∀ Z ∈ Q, mean P ⇑Z - lam * gini P ⇑Z ≤ mean P ⇑X - lam * gini P ⇑X) ∧
      ∀ X ∈ Q, (∀ Z ∈ Q, mean P ⇑Z - lam * gini P ⇑Z ≤ mean P ⇑X - lam * gini P ⇑X) →
        SSDEfficient P ((fun Z : Lp ℝ q P => (⇑Z : Ω → ℝ)) '' Q) ⇑X := by
  have hp : 0 < q.toReal := ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hq)) hqtop
  have hfl := DualSSD.MeanRiskProof.objective_lipschitz P q lam hlam0.le hlam1
  obtain ⟨M0, hM0⟩ := hQbdd.exists_norm_le
  let M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound : ∀ X ∈ Q, ‖X‖ ≤ M := fun X hX => (hM0 X hX).trans (le_max_left _ _)
  have hF : Continuous (fun X : Lp ℝ q P => ‖X‖ ^ q.toReal) :=
    continuous_norm.rpow_const (fun _ => Or.inr hp.le)
  have hFbound : ∀ X ∈ Q, ‖X‖ ^ q.toReal ≤ M ^ q.toReal :=
    fun X hX => Real.rpow_le_rpow (norm_nonneg X) (hbound X hX) hp.le
  have hfbdd : BddAbove ((fun X : Lp ℝ q P => DualSSD.MeanRiskProof.objective P lam X) '' Q) := by
    refine ⟨DualSSD.MeanRiskProof.objective P lam (0 : Lp ℝ q P) + 2*M, ?_⟩
    rintro _ ⟨X,hX,rfl⟩
    have hh := hfl.dist_le_mul X 0
    simp only [Real.dist_eq, dist_zero_right, NNReal.coe_ofNat] at hh
    have hb := hbound X hX
    have ha := le_abs_self (DualSSD.MeanRiskProof.objective P lam X -
      DualSSD.MeanRiskProof.objective P lam (0 : Lp ℝ q P))
    linarith
  obtain ⟨X,hX,hmax⟩ := DualSSD.MeanRiskProof.exists_max_of_midpoint_control hF
    (DualSSD.MeanRiskProof.lp_midpoint_control P q hq hqtop)
    (fun X => Real.rpow_nonneg (norm_nonneg X) _) hQne hQclosed hfl.continuous
    ((DualSSD.MeanRiskProof.objective_concave P q lam hlam0.le).subset
      (Set.subset_univ Q) hQconv) hM hbound hFbound hfbdd
  refine ⟨⟨X,hX,hmax⟩, ?_⟩
  intro X _hX hopt
  rintro ⟨_,⟨Y,hY,rfl⟩,hdom⟩
  have hh := DualSSD.MeanRiskProof.objective_strict_ssd P q lam hlam0 hlam1 X Y hdom
  exact (not_lt_of_ge (hopt Y hY)) hh

end DualSSD.MeanRisk

end

open DualSSD.MeanRisk
open MeasureTheory


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (q : ENNReal) [Fact (1 ≤ q)] (hq : 1 < q) (hqtop : q ≠ ⊤)
    (Q : Set (Lp ℝ q P)) (hQconv : Convex ℝ Q) (hQbdd : Bornology.IsBounded Q)
    (hQclosed : IsClosed Q) (hQne : Q.Nonempty) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (∃ X ∈ Q, ∀ Z ∈ Q, mean P ⇑Z - lam * gini P ⇑Z ≤ mean P ⇑X - lam * gini P ⇑X) ∧
      ∀ X ∈ Q, (∀ Z ∈ Q, mean P ⇑Z - lam * gini P ⇑Z ≤ mean P ⇑X - lam * gini P ⇑X) →
        SSDEfficient P ((fun Z : Lp ℝ q P => (⇑Z : Ω → ℝ)) '' Q) ⇑X := by
  exact DualSSD.MeanRisk.meanGini_optimal_exists_ssdEfficient P q hq hqtop Q hQconv hQbdd hQclosed hQne lam hlam0 hlam1

#print axioms DualSSD.MeanRisk.meanGini_optimal_exists_ssdEfficient
#print axioms solution
