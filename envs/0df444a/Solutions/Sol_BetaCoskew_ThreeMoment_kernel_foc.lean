-- Prove2me | solution 1 for BetaCoskew.ThreeMoment.kernel_foc
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T18:04:14.34698+00:00
-- url     : https://prove2.me/submissions/c5d1d8f5-87e2-4e37-a180-49284eecc6ce

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model


open MeasureTheory ProbabilityTheory Filter Topology Set BetaCoskew.ThreeMoment

namespace BCK

/-- A cdf is continuous iff the measure has no atoms. -/
lemma cdf_continuous_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Continuous (cdf μ) ↔ ∀ c, μ {c} = 0 := by
  have key : ∀ c, μ {c} = ENNReal.ofReal (cdf μ c - Function.leftLim (cdf μ) c) := by
    intro c; rw [← (cdf μ).measure_singleton, measure_cdf]
  constructor
  · intro h c
    rw [key]
    have : Function.leftLim (cdf μ) c = cdf μ c :=
      (cdf μ).mono.continuousWithinAt_Iio_iff_leftLim_eq.1 h.continuousAt.continuousWithinAt
    simp [this]
  · intro h
    rw [continuous_iff_continuousAt]; intro c
    rw [(cdf μ).mono.continuousAt_iff_leftLim_eq_rightLim, (cdf μ).rightLim_eq]
    have h1 := key c
    rw [h c] at h1
    have h2 : cdf μ c - Function.leftLim (cdf μ) c ≤ 0 := ENNReal.ofReal_eq_zero.1 h1.symm
    have h3 : Function.leftLim (cdf μ) c ≤ cdf μ c := (cdf μ).mono.leftLim_le le_rfl
    linarith

/-- Rank invariance: the cdf of a strictly increasing transform. -/
lemma cdf_map_comp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) {φ : ℝ → ℝ} (hφ : StrictMono φ)
    (hφm : Measurable φ) (x : ℝ) :
    cdf (P.map (fun ω => φ (X ω))) (φ x) = cdf (P.map X) x := by
  have hc : AEMeasurable (fun ω => φ (X ω)) P := hφm.comp_aemeasurable hX
  haveI := Measure.isProbabilityMeasure_map hX
  haveI := Measure.isProbabilityMeasure_map hc
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable hc measurableSet_Iic,
    Measure.map_apply_of_aemeasurable hX measurableSet_Iic]
  congr 2
  ext ω
  simp [hφ.le_iff_le]

/-- A strictly increasing transform of an atomless variable is atomless. -/
lemma noAtoms_map_comp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Ω → ℝ} (hX : AEMeasurable X P) {φ : ℝ → ℝ} (hφ : StrictMono φ)
    (hφm : Measurable φ) (hna : ∀ c, P.map X {c} = 0) (c : ℝ) :
    P.map (fun ω => φ (X ω)) {c} = 0 := by
  have hc : AEMeasurable (fun ω => φ (X ω)) P := hφm.comp_aemeasurable hX
  rw [Measure.map_apply_of_aemeasurable hc (measurableSet_singleton c)]
  by_cases h : ∃ x, φ x = c
  · obtain ⟨x, rfl⟩ := h
    have := hna x
    rw [Measure.map_apply_of_aemeasurable hX (measurableSet_singleton x)] at this
    refine measure_mono_null (fun ω hω => ?_) this
    simp only [mem_preimage, mem_singleton_iff] at hω ⊢
    exact hφ.injective hω
  · push Not at h
    have : (fun ω => φ (X ω)) ⁻¹' {c} = ∅ := by
      ext ω; simp [h (X ω)]
    rw [this, measure_empty]

/-- Representation of the RDU objective as an expectation on `Ω`. -/
lemma rdu_repr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u w : ℝ → ℝ) (hu : ContinuousOn u (Ioi 0)) {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hpos : ∀ᵐ ω ∂P, 0 < X ω) :
    rdu P u w X = ∫ ω, u (X ω) * deriv w (1 - cdf (P.map X) (X ω)) ∂P ∧
    (RduIntegrable P u w X ↔
      Integrable (fun ω => u (X ω) * deriv w (1 - cdf (P.map X) (X ω))) P) := by
  have hrestr : (P.map X).restrict (Ioi 0) = P.map X := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact (ae_map_iff hX measurableSet_Ioi).2 hpos
  have hG : AEStronglyMeasurable (fun x => u x * deriv w (1 - cdf (P.map X) x)) (P.map X) := by
    have h1 : AEStronglyMeasurable u (P.map X) := by
      rw [← hrestr]; exact hu.aestronglyMeasurable measurableSet_Ioi
    have h2 : Measurable (fun x => deriv w (1 - cdf (P.map X) x)) :=
      (measurable_deriv w).comp (measurable_const.sub (cdf (P.map X)).mono.measurable)
    exact h1.mul h2.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · unfold rdu
    exact integral_map hX hG
  · unfold RduIntegrable
    exact integrable_map_measure hG hX

/-- Probability integral transform: for a continuous cdf `F` and `0 ≤ t < 1`,
`μ {F ≤ t} = t`. -/
lemma measure_cdf_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (hF : Continuous (cdf μ))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    μ {x | cdf μ x ≤ t} = ENNReal.ofReal t := by
  set S := {x | cdf μ x ≤ t} with hS
  have hclosed : IsClosed S := isClosed_le hF continuous_const
  -- bounded above
  have hev : ∀ᶠ x in atTop, t < cdf μ x := (tendsto_cdf_atTop μ).eventually (lt_mem_nhds ht1)
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  have hbdd : BddAbove S := ⟨M, fun x hx => by
    by_contra h; push Not at h
    exact absurd hx (not_le.2 (hM x h.le))⟩
  rcases S.eq_empty_or_nonempty with hempty | hne
  · rw [hempty, measure_empty]
    rcases ht0.lt_or_eq with ht | ht
    · exfalso
      have hev2 : ∀ᶠ x in atBot, cdf μ x < t := (tendsto_cdf_atBot μ).eventually (gt_mem_nhds ht)
      obtain ⟨x, hx⟩ := hev2.exists
      have : x ∈ S := le_of_lt hx
      rw [hempty] at this; exact this
    · rw [← ht]; simp
  · set xs := sSup S
    have hxs : xs ∈ S := hclosed.csSup_mem hne hbdd
    have hSeq : S = Iic xs := by
      ext x; constructor
      · intro hx; exact le_csSup hbdd hx
      · intro hx; exact le_trans ((cdf μ).mono hx) hxs
    have hval : cdf μ xs = t := by
      refine le_antisymm hxs ?_
      by_contra hlt; push Not at hlt
      have hev3 : ∀ᶠ y in 𝓝 xs, cdf μ y < t := hF.continuousAt.eventually (gt_mem_nhds hlt)
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev3
      have hy : xs + ε / 2 ∈ S := by
        have := hball (xs + ε / 2) (by
          rw [Metric.mem_ball, Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
        exact le_of_lt (by simpa using this)
      have := le_csSup hbdd hy
      linarith
    rw [hSeq, ← ofReal_cdf, hval]

/-- Quantile function of a probability measure on `ℝ`. -/
noncomputable def quant (μ : Measure ℝ) (s : ℝ) : ℝ := sInf {x | s ≤ cdf μ x}

/-- Galois connection for the quantile of a continuous cdf. -/
lemma quant_le_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (hF : Continuous (cdf μ))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (x : ℝ) :
    quant μ s ≤ x ↔ s ≤ cdf μ x := by
  set T := {x | s ≤ cdf μ x} with hT
  have hclosed : IsClosed T := isClosed_le continuous_const hF
  have hev : ∀ᶠ x in atTop, s < cdf μ x := (tendsto_cdf_atTop μ).eventually (lt_mem_nhds hs1)
  have hne : T.Nonempty := by
    obtain ⟨x, hx⟩ := hev.exists; exact ⟨x, le_of_lt hx⟩
  have hev2 : ∀ᶠ x in atBot, cdf μ x < s := (tendsto_cdf_atBot μ).eventually (gt_mem_nhds hs0)
  obtain ⟨L, hL⟩ := eventually_atBot.1 hev2
  have hbdd : BddBelow T := ⟨L, fun x hx => by
    by_contra h; push Not at h
    exact absurd hx (not_le.2 (hL x h.le))⟩
  have hmem : quant μ s ∈ T := hclosed.csInf_mem hne hbdd
  constructor
  · intro h; exact le_trans hmem ((cdf μ).mono h)
  · intro h; exact csInf_le hbdd h

end BCK


open MeasureTheory ProbabilityTheory Filter Topology Set BetaCoskew.ThreeMoment

namespace BCK

/-- Basic calculus facts about the utility. -/
lemma u_props {u : ℝ → ℝ} (hu : UtilityAssumption u) :
    (∀ x, 0 < x → HasDerivAt u (deriv u x) x) ∧ AntitoneOn (deriv u) (Ioi 0) ∧
      (∀ x, 0 < x → 0 < deriv u x) := by
  have hd : ∀ x, 0 < x → DifferentiableAt ℝ u x := fun x hx =>
    (hu.contDiffOn.differentiableOn (by norm_num) x hx).differentiableAt (Ioi_mem_nhds hx)
  have hanti : AntitoneOn (deriv u) (Ioi 0) :=
    hu.strictConcaveOn.concaveOn.antitoneOn_deriv (fun x hx => hd x hx)
  have hnn : ∀ x, 0 < x → 0 ≤ deriv u x := by
    intro x hx
    have := (hu.strictMonoOn.monotoneOn).derivWithin_nonneg (x := x)
    rwa [derivWithin_of_isOpen isOpen_Ioi hx] at this
  refine ⟨fun x hx => (hd x hx).hasDerivAt, hanti, ?_⟩
  intro x hx
  rcases (hnn x hx).lt_or_eq with h | h
  · exact h
  · exfalso
    -- u' vanishes on [x, ∞), contradicting strict monotonicity
    have hzero : ∀ y, x ≤ y → deriv u y = 0 := by
      intro y hy
      have h1 := hanti (show x ∈ Ioi (0:ℝ) from hx) (show y ∈ Ioi (0:ℝ) from by
        simp only [mem_Ioi]; linarith) hy
      have h2 := hnn y (by linarith)
      linarith
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope u (show x < x + 1 by linarith)
      (fun y hy => (hd y (by linarith [hy.1])).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (by linarith [hy.1])).differentiableWithinAt)
    rw [hzero c hc.1.le] at hcd
    have hlt := hu.strictMonoOn (show x ∈ Ioi (0:ℝ) from hx)
      (show x + 1 ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; linarith) (by linarith : x < x + 1)
    have : u (x + 1) - u x = 0 := by
      have h3 : (x + 1 - x) ≠ 0 := by norm_num
      field_simp at hcd
      linarith
    linarith

/-- Basic facts about the probability weighting function on the open unit interval. -/
lemma w_props {w : ℝ → ℝ} (hw : WeightingAssumption w) :
    (∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt w (deriv w t) t) ∧
    (∃ C, ∀ t ∈ Ioo (0:ℝ) 1, 0 ≤ deriv w t ∧ deriv w t ≤ C) ∧
    (∫ t in (0:ℝ)..1, deriv w t) = 1 := by
  have hdiff : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt w (deriv w t) t := fun t ht =>
    ((hw.contDiffOn.differentiableOn (by norm_num) t (Ioo_subset_Icc_self ht)).differentiableAt
      (Icc_mem_nhds ht.1 ht.2)).hasDerivAt
  have heq : ∀ t ∈ Ioo (0:ℝ) 1, derivWithin w (Icc 0 1) t = deriv w t := fun t ht =>
    derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  have hcont : ContinuousOn (derivWithin w (Icc 0 1)) (Icc 0 1) :=
    hw.contDiffOn.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨hdiff, ⟨C, fun t ht => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [← heq t ht]
    exact (hw.strictMonoOn.monotoneOn).derivWithin_nonneg
  · rw [← heq t ht]
    exact le_trans (le_abs_self _) (hC t (Ioo_subset_Icc_self ht))
  · have hint : IntervalIntegrable (deriv w) volume 0 1 := by
      have h1 : IntegrableOn (derivWithin w (Icc 0 1)) (Ioc 0 1) :=
        (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 (h1.congr_fun_ae ?_)
      have hnull : volume ({1} : Set ℝ) = 0 := measure_singleton 1
      refine (ae_restrict_iff' (measurableSet_Ioc (a := (0:ℝ)) (b := 1))).2 ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with t ht1 ht
      exact heq t ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      hw.contDiffOn.continuousOn hdiff hint, hw.one, hw.zero]
    norm_num

/-- The law of `F(X)` is uniform on `[0,1]` when `F` is continuous. -/
lemma map_cdf_eq_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ] (hF : Continuous (cdf μ)) :
    μ.map (cdf μ) = volume.restrict (Icc 0 1) := by
  have hm : Measurable (cdf μ) := (cdf μ).mono.measurable
  have : IsFiniteMeasure (μ.map (cdf μ)) := Measure.isFiniteMeasure_map μ _
  refine Measure.ext_of_Iic _ _ (fun t => ?_)
  rw [Measure.map_apply hm measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  have hpre : cdf μ ⁻¹' Iic t = {x | cdf μ x ≤ t} := rfl
  rw [hpre]
  rcases lt_or_ge t 0 with ht | ht
  · have h1 : {x | cdf μ x ≤ t} = ∅ := by
      ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le ht (cdf_nonneg μ x)
    have h2 : Iic t ∩ Icc (0:ℝ) 1 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      intro h; linarith [h.1, h.2.1]
    rw [h1, h2]; simp
  rcases lt_or_ge t 1 with ht1 | ht1
  · rw [measure_cdf_le μ hF ht ht1]
    have h2 : Iic t ∩ Icc (0:ℝ) 1 = Icc 0 t := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [h2, Real.volume_Icc, sub_zero]
  · have h1 : {x | cdf μ x ≤ t} = univ := by
      ext x; simp only [mem_setOf_eq, mem_univ, iff_true]
      exact le_trans (cdf_le_one μ x) ht1
    have h2 : Iic t ∩ Icc (0:ℝ) 1 = Icc 0 1 := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro h; exact ⟨by linarith [h.2], h⟩
    rw [h1, h2, Real.volume_Icc, measure_univ]
    simp

end BCK


open MeasureTheory ProbabilityTheory Filter Topology Set BetaCoskew.ThreeMoment

namespace BCK

/-- The standing hypotheses of the first-order condition. -/
structure Ctx {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (u w : ℝ → ℝ)
    (mt RM : Ω → ℝ) : Prop where
  hu : UtilityAssumption u
  hw : WeightingAssumption w
  mt_meas : Measurable mt
  mt_pos : ∀ᵐ ω ∂P, 0 < mt ω
  mt_int : Integrable mt P
  RM_meas : Measurable RM
  hEq : IsEquilibrium P u w mt RM
  hF : Continuous (cdf (P.map RM))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {u w : ℝ → ℝ} {mt RM : Ω → ℝ}

namespace Ctx

lemma u_cont (h : Ctx P u w mt RM) : ContinuousOn u (Ioi 0) :=
  h.hu.contDiffOn.continuousOn

lemma probMap (h : Ctx P u w mt RM) : IsProbabilityMeasure (P.map RM) :=
  Measure.isProbabilityMeasure_map h.RM_meas.aemeasurable

lemma noAtoms (h : Ctx P u w mt RM) (c : ℝ) : P.map RM {c} = 0 := by
  have := h.probMap
  exact (cdf_continuous_iff _).1 h.hF c

lemma noAtoms' (h : Ctx P u w mt RM) (c : ℝ) : P {ω | RM ω = c} = 0 := by
  have := h.noAtoms c
  rwa [Measure.map_apply h.RM_meas (measurableSet_singleton c)] at this

lemma pos (h : Ctx P u w mt RM) : ∀ᵐ ω ∂P, 0 < RM ω := by
  have h0 : ∀ᵐ ω ∂P, RM ω ≠ 0 := by
    rw [ae_iff]; simpa using h.noAtoms' 0
  filter_upwards [h.hEq.1.2.2.2, h0] with ω h1 h2
  exact lt_of_le_of_ne h1 (Ne.symm h2)

lemma uniform (h : Ctx P u w mt RM) :
    (P.map RM).map (cdf (P.map RM)) = volume.restrict (Icc 0 1) := by
  have := h.probMap
  exact map_cdf_eq_uniform _ h.hF

lemma F_mem (h : Ctx P u w mt RM) : ∀ᵐ ω ∂P, cdf (P.map RM) (RM ω) ∈ Ioo (0:ℝ) 1 := by
  have hm : Measurable (cdf (P.map RM)) := (cdf (P.map RM)).mono.measurable
  have hnull : (P.map RM).map (cdf (P.map RM)) ({0, 1} : Set ℝ) = 0 := by
    rw [h.uniform, Measure.restrict_apply (by measurability)]
    exact measure_mono_null inter_subset_left (Set.Finite.measure_zero (by simp) _)
  rw [Measure.map_apply hm (by measurability),
    Measure.map_apply h.RM_meas (hm (by measurability))] at hnull
  have hle : ∀ᵐ ω ∂P, cdf (P.map RM) (RM ω) ∉ ({0, 1} : Set ℝ) := by
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hnull
    simp only [mem_setOf_eq, not_not] at hω
    exact hω
  filter_upwards [hle] with ω hω
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hω
  have := h.probMap
  exact ⟨lt_of_le_of_ne (cdf_nonneg _ _) (Ne.symm hω.1),
    lt_of_le_of_ne (cdf_le_one _ _) hω.2⟩

/-- The rank weight `Ψ = w'(1 - F(R_M))` is a.s. bounded. -/
lemma psi_bdd (h : Ctx P u w mt RM) : ∃ C, ∀ᵐ ω ∂P,
    0 ≤ deriv w (1 - cdf (P.map RM) (RM ω)) ∧ deriv w (1 - cdf (P.map RM) (RM ω)) ≤ C := by
  obtain ⟨-, ⟨C, hC⟩, -⟩ := w_props h.hw
  refine ⟨C, ?_⟩
  filter_upwards [h.F_mem] with ω hω
  exact hC _ ⟨by linarith [hω.2], by linarith [hω.1]⟩

lemma psi_meas (h : Ctx P u w mt RM) :
    Measurable (fun ω => deriv w (1 - cdf (P.map RM) (RM ω))) :=
  (measurable_deriv w).comp
    (measurable_const.sub ((cdf (P.map RM)).mono.measurable.comp h.RM_meas))

lemma psi_int (h : Ctx P u w mt RM) :
    Integrable (fun ω => deriv w (1 - cdf (P.map RM) (RM ω))) P := by
  obtain ⟨C, hC⟩ := h.psi_bdd
  refine Integrable.of_bound (C := C) h.psi_meas.aestronglyMeasurable ?_
  filter_upwards [hC] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2

/-- `E[w'(1 - F(R_M))] = 1`. -/
lemma psi_integral (h : Ctx P u w mt RM) :
    ∫ ω, deriv w (1 - cdf (P.map RM) (RM ω)) ∂P = 1 := by
  obtain ⟨-, -, hI⟩ := w_props h.hw
  have hm : Measurable (cdf (P.map RM)) := (cdf (P.map RM)).mono.measurable
  have hg : Measurable (fun t : ℝ => deriv w (1 - t)) :=
    (measurable_deriv w).comp (measurable_const.sub measurable_id)
  have e1 : (∫ ω, deriv w (1 - cdf (P.map RM) (RM ω)) ∂P) =
      ∫ x, deriv w (1 - cdf (P.map RM) x) ∂(P.map RM) :=
    (integral_map h.RM_meas.aemeasurable
      (hg.comp hm).aestronglyMeasurable).symm
  have e2 : (∫ x, deriv w (1 - cdf (P.map RM) x) ∂(P.map RM)) =
      ∫ t, deriv w (1 - t) ∂((P.map RM).map (cdf (P.map RM))) :=
    (integral_map hm.aemeasurable hg.aestronglyMeasurable).symm
  rw [e1, e2, h.uniform, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
    zero_le_one, intervalIntegral.integral_comp_sub_left (fun t => deriv w t) 1]
  simpa using hI

/-- Admissible comparators cannot beat the market return. -/
lemma adm (h : Ctx P u w mt RM) {X : Ω → ℝ} (hXm : Measurable X) (hXpos : ∀ᵐ ω ∂P, 0 < X ω)
    (hXna : ∀ c, P.map X {c} = 0) (hint : Integrable (fun ω => mt ω * X ω) P)
    (hbud : ∫ ω, mt ω * X ω ∂P = 1)
    (hrdu : Integrable (fun ω => u (X ω) * deriv w (1 - cdf (P.map X) (X ω))) P) :
    (∫ ω, u (X ω) * deriv w (1 - cdf (P.map X) (X ω)) ∂P) ≤
      ∫ ω, u (RM ω) * deriv w (1 - cdf (P.map RM) (RM ω)) ∂P := by
  have : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hXm.aemeasurable
  obtain ⟨eX, iX⟩ := rdu_repr P u w h.u_cont hXm.aemeasurable hXpos
  obtain ⟨eR, -⟩ := rdu_repr P u w h.u_cont h.RM_meas.aemeasurable h.pos
  rw [← eX, ← eR]
  refine h.hEq.2.2 X ⟨hXm, hint, hbud, hXpos.mono fun ω hω => hω.le⟩ (iX.2 hrdu)
    ((cdf_continuous_iff _).2 hXna) hXpos

lemma rdu_int (h : Ctx P u w mt RM) :
    Integrable (fun ω => u (RM ω) * deriv w (1 - cdf (P.map RM) (RM ω))) P :=
  (rdu_repr P u w h.u_cont h.RM_meas.aemeasurable h.pos).2.1 h.hEq.2.1

lemma budget (h : Ctx P u w mt RM) : ∫ ω, mt ω * RM ω ∂P = 1 := h.hEq.1.2.2.1

lemma budget_int (h : Ctx P u w mt RM) : Integrable (fun ω => mt ω * RM ω) P := h.hEq.1.2.1

/-- A.e.-strong measurability of `u ∘ X` for an a.s. positive measurable `X`. -/
lemma aesm_u (h : Ctx P u w mt RM) {X : Ω → ℝ} (hXm : Measurable X) (hXpos : ∀ᵐ ω ∂P, 0 < X ω) :
    AEStronglyMeasurable (fun ω => u (X ω)) P := by
  have hrestr : (P.map X).restrict (Ioi 0) = P.map X := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact (ae_map_iff hXm.aemeasurable measurableSet_Ioi).2 hXpos
  have h1 : AEStronglyMeasurable u (P.map X) := by
    rw [← hrestr]; exact h.u_cont.aestronglyMeasurable measurableSet_Ioi
  exact h1.comp_aemeasurable hXm.aemeasurable

end Ctx

end BCK


open MeasureTheory ProbabilityTheory Filter Topology Set BetaCoskew.ThreeMoment

namespace BCK

/-- Piecewise-linear ramp from `0` (below `a`) to `1` (above `a + η`). -/
noncomputable def ramp (a η x : ℝ) : ℝ := max 0 (min 1 ((x - a) / η))

lemma ramp_nonneg (a η x : ℝ) : 0 ≤ ramp a η x := le_max_left _ _

lemma ramp_le_one (a η x : ℝ) : ramp a η x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma ramp_of_le {a η x : ℝ} (hη : 0 < η) (hx : x ≤ a) : ramp a η x = 0 := by
  unfold ramp
  have : (x - a) / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hη.le
  exact max_eq_left (le_trans (min_le_right _ _) this)

lemma ramp_continuous (a η : ℝ) : Continuous (ramp a η) := by
  unfold ramp; fun_prop

lemma ramp_lip {a η : ℝ} (hη : 0 < η) (x y : ℝ) :
    |ramp a η y - ramp a η x| ≤ |y - x| / η := by
  unfold ramp
  have h1 : |max 0 (min 1 ((y - a) / η)) - max 0 (min 1 ((x - a) / η))| ≤
      |min 1 ((y - a) / η) - min 1 ((x - a) / η)| := by
    rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
  have h2 : |min 1 ((y - a) / η) - min 1 ((x - a) / η)| ≤ |(y - a) / η - (x - a) / η| :=
    abs_min_sub_min_le_max _ _ _ _ |>.trans (by simp)
  have h3 : |(y - a) / η - (x - a) / η| = |y - x| / η := by
    rw [← sub_div, abs_div, abs_of_pos hη]; ring_nf
  linarith

lemma ramp_tendsto (a x : ℝ) :
    Tendsto (fun n : ℕ => ramp a (1 / ((n : ℝ) + 1)) x) atTop
      (𝓝 ((Ioi a).indicator (fun _ => (1:ℝ)) x)) := by
  by_cases hx : a < x
  · rw [indicator_of_mem (show x ∈ Ioi a from hx)]
    have hev : ∀ᶠ n : ℕ in atTop, ramp a (1 / ((n : ℝ) + 1)) x = 1 := by
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - a))
      refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      unfold ramp
      have hpos : (0:ℝ) < (n : ℝ) + 1 := by positivity
      have : 1 ≤ (x - a) / (1 / ((n : ℝ) + 1)) := by
        rw [div_div_eq_mul_div, div_one]
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        have : 1 / (x - a) < (n : ℝ) + 1 := by linarith
        rw [div_lt_iff₀ (by linarith)] at this
        nlinarith
      rw [min_eq_left this]; simp
    exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)
  · rw [indicator_of_notMem (show x ∉ Ioi a from hx)]
    push Not at hx
    have : ∀ n : ℕ, ramp a (1 / ((n : ℝ) + 1)) x = 0 := fun n =>
      ramp_of_le (by positivity) hx
    simp only [this]; exact tendsto_const_nhds

namespace Ctx

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {u w : ℝ → ℝ} {mt RM : Ω → ℝ}

/-- Lipschitz bound for `u` away from zero. -/
lemma u_lip (h : Ctx P u w mt RM) {c : ℝ} (hc : 0 < c) {x y : ℝ} (hx : c ≤ x) (hy : c ≤ y) :
    |u y - u x| ≤ deriv u c * |y - x| := by
  obtain ⟨hd, hanti, hpos⟩ := u_props h.hu
  have := (convex_Ici c).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := u) (f' := deriv u) (C := deriv u c)
    (fun z hz => (hd z (lt_of_lt_of_le hc hz)).hasDerivWithinAt)
    (fun z hz => by
      rw [Real.norm_eq_abs, abs_of_pos (hpos z (lt_of_lt_of_le hc hz))]
      exact hanti (show c ∈ Ioi (0:ℝ) from hc) (show z ∈ Ioi (0:ℝ) from lt_of_lt_of_le hc hz) hz)
    (show x ∈ Ici c from hx) (show y ∈ Ici c from hy)
  simpa [Real.norm_eq_abs] using this

/-- First-order condition along a rank-preserving ramp perturbation. -/
lemma foc_ramp (h : Ctx P u w mt RM) {a b η κ : ℝ} (ha : 0 < a) (hb : 0 < b) (hη : 0 < η)
    (hκ : 0 ≤ κ)
    (hbal : ∫ ω, mt ω * (ramp a η (RM ω) - κ * ramp b η (RM ω)) ∂P = 0) :
    ∫ ω, deriv u (RM ω) * (ramp a η (RM ω) - κ * ramp b η (RM ω)) *
      deriv w (1 - cdf (P.map RM) (RM ω)) ∂P = 0 := by
  obtain ⟨hd, hanti, hupos⟩ := u_props h.hu
  obtain ⟨C, hC⟩ := h.psi_bdd
  set H : ℝ → ℝ := fun x => ramp a η x - κ * ramp b η x with hHdef
  set Ψ : Ω → ℝ := fun ω => deriv w (1 - cdf (P.map RM) (RM ω)) with hΨ
  set m := min a b with hm
  have hm0 : 0 < m := lt_min ha hb
  have hHc : Continuous H := (ramp_continuous a η).sub (continuous_const.mul (ramp_continuous b η))
  have hHbdd : ∀ x, |H x| ≤ 1 + κ := by
    intro x
    have h1 := ramp_nonneg a η x; have h2 := ramp_le_one a η x
    have h3 := ramp_nonneg b η x; have h4 := ramp_le_one b η x
    rw [abs_le]; constructor <;> nlinarith
  have hHzero : ∀ x, x ≤ m → H x = 0 := by
    intro x hx
    simp only [hHdef, ramp_of_le hη (le_trans hx (min_le_left a b)),
      ramp_of_le hη (le_trans hx (min_le_right a b))]; ring
  have hHlip : ∀ x y, |H y - H x| ≤ (1 + κ) / η * |y - x| := by
    intro x y
    have e : H y - H x = (ramp a η y - ramp a η x) - κ * (ramp b η y - ramp b η x) := by
      simp only [hHdef]; ring
    rw [e]
    have l1 := ramp_lip (a := a) hη x y
    have l2 := ramp_lip (a := b) hη x y
    calc |ramp a η y - ramp a η x - κ * (ramp b η y - ramp b η x)|
        ≤ |ramp a η y - ramp a η x| + |κ * (ramp b η y - ramp b η x)| := abs_sub _ _
      _ = |ramp a η y - ramp a η x| + κ * |ramp b η y - ramp b η x| := by
          rw [abs_mul, abs_of_nonneg hκ]
      _ ≤ |y - x| / η + κ * (|y - x| / η) := by gcongr
      _ = (1 + κ) / η * |y - x| := by ring
  set ε0 := min (η / (2 * (1 + κ))) (m / (2 * (1 + κ))) with hε0
  have hε0pos : 0 < ε0 := lt_min (by positivity) (by positivity)
  have hε0a : ε0 * (1 + κ) ≤ η / 2 := by
    have : ε0 ≤ η / (2 * (1 + κ)) := min_le_left _ _
    calc ε0 * (1 + κ) ≤ η / (2 * (1 + κ)) * (1 + κ) := by gcongr
      _ = η / 2 := by field_simp
  have hε0b : ε0 * (1 + κ) ≤ m / 2 := by
    have : ε0 ≤ m / (2 * (1 + κ)) := min_le_right _ _
    calc ε0 * (1 + κ) ≤ m / (2 * (1 + κ)) * (1 + κ) := by gcongr
      _ = m / 2 := by field_simp
  -- the perturbed payoff
  have hmono : ∀ ε, |ε| < ε0 → StrictMono (fun x => x + ε * H x) := by
    intro ε hε x y hxy
    have hl := hHlip x y
    have h1 : |ε * (H y - H x)| ≤ |ε| * ((1 + κ) / η * |y - x|) := by
      rw [abs_mul]; gcongr
    have h2 : |ε| * ((1 + κ) / η * |y - x|) ≤ (y - x) / 2 := by
      rw [abs_of_pos (sub_pos.2 hxy)]
      have : |ε| * (1 + κ) ≤ η / 2 := le_trans (by gcongr) hε0a
      calc |ε| * ((1 + κ) / η * (y - x)) = (|ε| * (1 + κ)) / η * (y - x) := by ring
        _ ≤ (η / 2) / η * (y - x) := by gcongr
        _ = (y - x) / 2 := by field_simp
    have h3 := neg_abs_le (ε * (H y - H x))
    show x + ε * H x < y + ε * H y
    nlinarith
  have hposφ : ∀ ε, |ε| < ε0 → ∀ x, 0 < x → 0 < x + ε * H x ∧
      (H x ≠ 0 → m / 2 ≤ x + ε * H x ∧ m < x) := by
    intro ε hε x hx
    by_cases hxm : x ≤ m
    · rw [hHzero x hxm]; simp [hx]
    · push Not at hxm
      have hb1 : |ε * H x| ≤ m / 2 := by
        rw [abs_mul]
        calc |ε| * |H x| ≤ ε0 * (1 + κ) := by
              gcongr; exact hHbdd x
          _ ≤ m / 2 := hε0b
      have := neg_abs_le (ε * H x)
      refine ⟨by linarith, fun _ => ⟨by linarith, hxm⟩⟩
  -- J(ε) ≤ J(0)
  set J : ℝ → ℝ := fun ε => ∫ ω, u (RM ω + ε * H (RM ω)) * Ψ ω ∂P with hJ
  have hRMpos := h.pos
  have hΨm : Measurable Ψ := h.psi_meas
  have hmtH : Integrable (fun ω => mt ω * H (RM ω)) P := by
    refine (h.mt_int.mul_bdd (c := 1 + κ) ((hHc.measurable.comp h.RM_meas).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)).congr (Eventually.of_forall fun ω => by simp [mul_comm])
    rw [Real.norm_eq_abs]; exact hHbdd _
  have hint_pert : ∀ ε, |ε| < ε0 →
      Integrable (fun ω => u (RM ω + ε * H (RM ω)) * Ψ ω) P := by
    intro ε hε
    have hdiff : ∀ᵐ ω ∂P, |u (RM ω + ε * H (RM ω)) * Ψ ω - u (RM ω) * Ψ ω| ≤
        deriv u (m / 2) * (ε0 * (1 + κ)) * C := by
      filter_upwards [hRMpos, hC] with ω hω hΨω
      rw [← sub_mul, abs_mul, abs_of_nonneg hΨω.1]
      by_cases hH : H (RM ω) = 0
      · rw [hH]; simp only [mul_zero, add_zero, sub_self, abs_zero, zero_mul]
        have := hupos (m / 2) (by positivity)
        have hC0 : 0 ≤ C := le_trans hΨω.1 hΨω.2
        exact mul_nonneg (mul_nonneg this.le (by positivity)) hC0
      · obtain ⟨hlo, hRM⟩ := (hposφ ε hε (RM ω) hω).2 hH
        have hl := h.u_lip (c := m / 2) (by positivity) (x := RM ω)
          (y := RM ω + ε * H (RM ω)) (by linarith) hlo
        have hstep : |RM ω + ε * H (RM ω) - RM ω| ≤ ε0 * (1 + κ) := by
          rw [add_sub_cancel_left, abs_mul]
          exact mul_le_mul hε.le (hHbdd _) (abs_nonneg _) hε0pos.le
        have hd0 : 0 ≤ deriv u (m / 2) := (hupos (m / 2) (by positivity)).le
        calc |u (RM ω + ε * H (RM ω)) - u (RM ω)| * Ψ ω
            ≤ (deriv u (m / 2) * (ε0 * (1 + κ))) * C := by
              apply mul_le_mul _ hΨω.2 hΨω.1 (by positivity)
              exact le_trans hl (mul_le_mul_of_nonneg_left hstep hd0)
          _ = deriv u (m / 2) * (ε0 * (1 + κ)) * C := by ring
    have hXm : Measurable (fun ω => RM ω + ε * H (RM ω)) :=
      h.RM_meas.add (measurable_const.mul (hHc.measurable.comp h.RM_meas))
    have hXpos : ∀ᵐ ω ∂P, 0 < RM ω + ε * H (RM ω) :=
      hRMpos.mono fun ω hω => (hposφ ε hε _ hω).1
    have hmeas : AEStronglyMeasurable (fun ω => u (RM ω + ε * H (RM ω)) * Ψ ω) P :=
      (h.aesm_u hXm hXpos).mul hΨm.aestronglyMeasurable
    have hb : Integrable (fun ω => u (RM ω + ε * H (RM ω)) * Ψ ω - u (RM ω) * Ψ ω) P :=
      Integrable.of_bound (hmeas.sub h.rdu_int.aestronglyMeasurable) _ hdiff
    exact (hb.add h.rdu_int).congr (Eventually.of_forall fun ω => by
      simp only [Pi.add_apply, hΨ]; ring)
  have hle : ∀ ε, |ε| < ε0 → J ε ≤ J 0 := by
    intro ε hε
    have hφm : Measurable (fun x => x + ε * H x) :=
      (continuous_id.add (continuous_const.mul hHc)).measurable
    have hXm : Measurable (fun ω => RM ω + ε * H (RM ω)) := hφm.comp h.RM_meas
    have hXpos : ∀ᵐ ω ∂P, 0 < RM ω + ε * H (RM ω) :=
      hRMpos.mono fun ω hω => (hposφ ε hε _ hω).1
    have hcdf : ∀ ω, cdf (P.map (fun ω => RM ω + ε * H (RM ω))) (RM ω + ε * H (RM ω)) =
        cdf (P.map RM) (RM ω) :=
      fun ω => cdf_map_comp P h.RM_meas.aemeasurable (φ := fun x => x + ε * H x)
        (hmono ε hε) hφm (RM ω)
    have hint : Integrable (fun ω => mt ω * (RM ω + ε * H (RM ω))) P := by
      refine (h.budget_int.add (hmtH.const_mul ε)).congr (Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply]; ring
    have hbud : ∫ ω, mt ω * (RM ω + ε * H (RM ω)) ∂P = 1 := by
      have e : (fun ω => mt ω * (RM ω + ε * H (RM ω))) =
          fun ω => mt ω * RM ω + ε * (mt ω * H (RM ω)) := by
        funext ω; ring
      rw [e, integral_add h.budget_int (hmtH.const_mul ε), integral_const_mul, h.budget]
      have : ∫ ω, mt ω * H (RM ω) ∂P = 0 := hbal
      rw [this]; ring
    have hrdu : Integrable (fun ω => u (RM ω + ε * H (RM ω)) *
        deriv w (1 - cdf (P.map (fun ω => RM ω + ε * H (RM ω))) (RM ω + ε * H (RM ω)))) P := by
      refine (hint_pert ε hε).congr (Eventually.of_forall fun ω => ?_)
      simp only [hΨ]; rw [hcdf ω]
    have := h.adm hXm hXpos (noAtoms_map_comp P h.RM_meas.aemeasurable
      (φ := fun x => x + ε * H x) (hmono ε hε) hφm h.noAtoms) hint hbud hrdu
    simp only [hcdf] at this
    simp only [hJ, zero_mul, add_zero]
    exact this
  -- differentiate J at 0
  have hball : Metric.ball (0:ℝ) ε0 ∈ 𝓝 (0:ℝ) := Metric.ball_mem_nhds 0 hε0pos
  have hmemball : ∀ ε ∈ Metric.ball (0:ℝ) ε0, |ε| < ε0 := fun ε hε => by
    simpa [Metric.mem_ball, Real.dist_eq] using hε
  have hFmeas : ∀ᶠ ε in 𝓝 (0:ℝ),
      AEStronglyMeasurable (fun ω => u (RM ω + ε * H (RM ω)) * Ψ ω) P := by
    filter_upwards [hball] with ε hε
    exact (hint_pert ε (hmemball ε hε)).aestronglyMeasurable
  have hFint : Integrable (fun ω => u (RM ω + 0 * H (RM ω)) * Ψ ω) P := by
    simpa using h.rdu_int
  have hF'meas : AEStronglyMeasurable
      (fun ω => deriv u (RM ω + 0 * H (RM ω)) * H (RM ω) * Ψ ω) P :=
    (((measurable_deriv u).comp (h.RM_meas.add (measurable_const.mul
      (hHc.measurable.comp h.RM_meas)))).aestronglyMeasurable.mul
      (hHc.measurable.comp h.RM_meas).aestronglyMeasurable).mul hΨm.aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂P, ∀ ε ∈ Metric.ball (0:ℝ) ε0,
      ‖deriv u (RM ω + ε * H (RM ω)) * H (RM ω) * Ψ ω‖ ≤ deriv u (m / 2) * (1 + κ) * C := by
    filter_upwards [hRMpos, hC] with ω hω hΨω
    intro ε hε
    have hε' := hmemball ε hε
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hΨω.1]
    have hC0 : 0 ≤ C := le_trans hΨω.1 hΨω.2
    have h0 : 0 ≤ deriv u (m / 2) := (hupos _ (by positivity)).le
    by_cases hH : H (RM ω) = 0
    · rw [hH, abs_zero, mul_zero, zero_mul]
      positivity
    · have hp := (hposφ ε hε' (RM ω) hω).1
      obtain ⟨hlo, -⟩ := (hposφ ε hε' (RM ω) hω).2 hH
      have h1 : |deriv u (RM ω + ε * H (RM ω))| ≤ deriv u (m / 2) := by
        rw [abs_of_pos (hupos _ hp)]
        exact hanti (show m / 2 ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; positivity)
          (show RM ω + ε * H (RM ω) ∈ Ioi (0:ℝ) from hp) hlo
      apply mul_le_mul _ hΨω.2 hΨω.1 (by positivity)
      exact mul_le_mul h1 (hHbdd _) (abs_nonneg _) h0
  have hdiffε : ∀ᵐ ω ∂P, ∀ ε ∈ Metric.ball (0:ℝ) ε0,
      HasDerivAt (fun ε => u (RM ω + ε * H (RM ω)) * Ψ ω)
        (deriv u (RM ω + ε * H (RM ω)) * H (RM ω) * Ψ ω) ε := by
    filter_upwards [hRMpos] with ω hω
    intro ε hε
    have hp := (hposφ ε (hmemball ε hε) (RM ω) hω).1
    have h1 : HasDerivAt (fun ε : ℝ => RM ω + ε * H (RM ω)) (H (RM ω)) ε := by
      simpa using ((hasDerivAt_id ε).mul_const (H (RM ω))).const_add (RM ω)
    exact ((hd _ hp).comp ε h1).mul_const (Ψ ω)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
    (bound := fun _ => deriv u (m / 2) * (1 + κ) * C) hball hFmeas hFint hF'meas hbound
    (integrable_const _) hdiffε
  obtain ⟨-, hJd⟩ := hderiv
  have hlocmax : IsLocalMax J 0 := by
    filter_upwards [hball] with ε hε
    exact hle ε (hmemball ε hε)
  have := hlocmax.hasDerivAt_eq_zero hJd
  simpa [hHdef, hΨ, mul_comm, mul_assoc, mul_left_comm] using this

end Ctx

end BCK


open MeasureTheory ProbabilityTheory Filter Topology Set BetaCoskew.ThreeMoment

namespace BCK

namespace Ctx

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {u w : ℝ → ℝ} {mt RM : Ω → ℝ}

/-- The marginal-utility weight `g = u'(R_M) w'(1 - F(R_M))`. -/
noncomputable def gfun (P : Measure Ω) (u w : ℝ → ℝ) (RM : Ω → ℝ) (ω : Ω) : ℝ :=
  deriv u (RM ω) * deriv w (1 - cdf (P.map RM) (RM ω))

lemma g_meas (h : Ctx P u w mt RM) : Measurable (gfun P u w RM) :=
  ((measurable_deriv u).comp h.RM_meas).mul h.psi_meas

lemma g_nonneg (h : Ctx P u w mt RM) : ∀ᵐ ω ∂P, 0 ≤ gfun P u w RM ω := by
  obtain ⟨-, -, hupos⟩ := u_props h.hu
  obtain ⟨C, hC⟩ := h.psi_bdd
  filter_upwards [h.pos, hC] with ω hω hΨ
  exact mul_nonneg (hupos _ hω).le hΨ.1

/-- On `{R_M > a}` the weight `g` is bounded. -/
lemma g_bdd (h : Ctx P u w mt RM) {a : ℝ} (ha : 0 < a) : ∃ K, 0 ≤ K ∧ ∀ᵐ ω ∂P,
    a < RM ω → |gfun P u w RM ω| ≤ K := by
  obtain ⟨-, hanti, hupos⟩ := u_props h.hu
  obtain ⟨C, hC⟩ := h.psi_bdd
  refine ⟨deriv u a * max C 0, mul_nonneg (hupos a ha).le (le_max_right _ _), ?_⟩
  filter_upwards [hC] with ω hΨ hω
  unfold gfun
  rw [abs_mul, abs_of_pos (hupos _ (lt_trans ha hω)), abs_of_nonneg hΨ.1]
  exact mul_le_mul (hanti (show a ∈ Ioi (0:ℝ) from ha) (show RM ω ∈ Ioi (0:ℝ) from
    lt_trans ha hω) hω.le) (le_trans hΨ.2 (le_max_left _ _)) hΨ.1 (hupos a ha).le

lemma int_g_ramp (h : Ctx P u w mt RM) {a η : ℝ} (ha : 0 < a) (hη : 0 < η) :
    Integrable (fun ω => gfun P u w RM ω * ramp a η (RM ω)) P := by
  obtain ⟨K, hK0, hK⟩ := g_bdd h ha
  refine Integrable.of_bound (C := K) ((g_meas h).mul ((ramp_continuous a η).measurable.comp
    h.RM_meas)).aestronglyMeasurable ?_
  filter_upwards [hK] with ω hω
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hx : a < RM ω
  · calc |gfun P u w RM ω| * |ramp a η (RM ω)| ≤ K * 1 := by
          apply mul_le_mul (hω hx) _ (abs_nonneg _) hK0
          rw [abs_of_nonneg (ramp_nonneg _ _ _)]; exact ramp_le_one _ _ _
      _ = K := mul_one K
  · push Not at hx
    rw [ramp_of_le hη hx, abs_zero, mul_zero]
    exact hK0

lemma int_g_tail (h : Ctx P u w mt RM) {a : ℝ} (ha : 0 < a) :
    Integrable (fun ω => (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * gfun P u w RM ω) P := by
  obtain ⟨K, hK0, hK⟩ := g_bdd h ha
  refine Integrable.of_bound (C := K) (((measurable_const.indicator measurableSet_Ioi).comp
    h.RM_meas).mul (g_meas h)).aestronglyMeasurable ?_
  filter_upwards [hK] with ω hω
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hx : a < RM ω
  · rw [indicator_of_mem (show RM ω ∈ Ioi a from hx), abs_one, one_mul]; exact hω hx
  · rw [indicator_of_notMem (show RM ω ∉ Ioi a from hx), abs_zero, zero_mul]; exact hK0

lemma int_mt_ramp (h : Ctx P u w mt RM) (a η : ℝ) :
    Integrable (fun ω => mt ω * ramp a η (RM ω)) P := by
  refine h.mt_int.mul_bdd (c := 1) ((ramp_continuous a η).measurable.comp
    h.RM_meas).aestronglyMeasurable (Eventually.of_forall fun ω => ?_) |>.congr
    (Eventually.of_forall fun ω => by simp [mul_comm])
  simp only [Function.comp_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (ramp_nonneg _ _ _)]; exact ramp_le_one _ _ _

lemma int_mt_tail (h : Ctx P u w mt RM) (a : ℝ) :
    Integrable (fun ω => (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * mt ω) P := by
  refine h.mt_int.bdd_mul (c := 1) (((measurable_const.indicator measurableSet_Ioi).comp
    h.RM_meas)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  by_cases hx : a < RM ω
  · rw [indicator_of_mem (show RM ω ∈ Ioi a from hx)]; simp
  · rw [indicator_of_notMem (show RM ω ∉ Ioi a from hx)]; simp

/-- The cross identity for ramps. -/
lemma cross_ramp (h : Ctx P u w mt RM) {a b η : ℝ} (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    (∫ ω, gfun P u w RM ω * ramp a η (RM ω) ∂P) * (∫ ω, mt ω * ramp b η (RM ω) ∂P) =
      (∫ ω, mt ω * ramp a η (RM ω) ∂P) * (∫ ω, gfun P u w RM ω * ramp b η (RM ω) ∂P) := by
  set Ma := ∫ ω, mt ω * ramp a η (RM ω) ∂P
  set Mb := ∫ ω, mt ω * ramp b η (RM ω) ∂P
  set Ga := ∫ ω, gfun P u w RM ω * ramp a η (RM ω) ∂P
  set Gb := ∫ ω, gfun P u w RM ω * ramp b η (RM ω) ∂P
  have hMb0 : 0 ≤ Mb := integral_nonneg_of_ae (h.mt_pos.mono fun ω hω =>
    mul_nonneg hω.le (ramp_nonneg _ _ _))
  rcases hMb0.lt_or_eq with hMb | hMb
  · set κ := Ma / Mb
    have hMa0 : 0 ≤ Ma := integral_nonneg_of_ae (h.mt_pos.mono fun ω hω =>
      mul_nonneg hω.le (ramp_nonneg _ _ _))
    have hκ : 0 ≤ κ := div_nonneg hMa0 hMb.le
    have hbal : ∫ ω, mt ω * (ramp a η (RM ω) - κ * ramp b η (RM ω)) ∂P = 0 := by
      have e : (fun ω => mt ω * (ramp a η (RM ω) - κ * ramp b η (RM ω))) =
          fun ω => mt ω * ramp a η (RM ω) - κ * (mt ω * ramp b η (RM ω)) := by
        funext ω; ring
      rw [e, integral_sub (int_mt_ramp h a η) ((int_mt_ramp h b η).const_mul κ),
        integral_const_mul]
      simp only [κ]; field_simp; ring
    have hfoc := foc_ramp h ha hb hη hκ hbal
    have e2 : (fun ω => deriv u (RM ω) * (ramp a η (RM ω) - κ * ramp b η (RM ω)) *
        deriv w (1 - cdf (P.map RM) (RM ω))) =
        fun ω => gfun P u w RM ω * ramp a η (RM ω) - κ * (gfun P u w RM ω * ramp b η (RM ω)) := by
      funext ω; unfold gfun; ring
    rw [e2, integral_sub (int_g_ramp h ha hη) ((int_g_ramp h hb hη).const_mul κ),
      integral_const_mul] at hfoc
    have : Ga = κ * Gb := by linarith
    rw [this]; simp only [κ]; field_simp
  · -- `Mb = 0` forces the ramp at `b` to vanish a.s.
    have hz : (fun ω => mt ω * ramp b η (RM ω)) =ᵐ[P] 0 := by
      have := (integral_eq_zero_iff_of_nonneg_ae (h.mt_pos.mono fun ω hω =>
        mul_nonneg hω.le (ramp_nonneg _ _ _)) (int_mt_ramp h b η)).1 hMb.symm
      exact this
    have hGb : Gb = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hz, h.mt_pos] with ω hω hpos
      simp only [Pi.zero_apply] at hω ⊢
      rcases mul_eq_zero.1 hω with h1 | h1
      · exact absurd h1 hpos.ne'
      · rw [h1, mul_zero]
    rw [← hMb, hGb]; ring


lemma lim_g (h : Ctx P u w mt RM) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => ∫ ω, gfun P u w RM ω * ramp a (1 / ((n : ℝ) + 1)) (RM ω) ∂P) atTop
      (𝓝 (∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * gfun P u w RM ω ∂P)) := by
  obtain ⟨K, hK0, hK⟩ := g_bdd h ha
  refine tendsto_integral_of_dominated_convergence (fun _ => K) (fun n =>
    (int_g_ramp h ha (by positivity)).aestronglyMeasurable) (integrable_const K)
    (fun n => ?_) (Eventually.of_forall fun ω => ?_)
  · filter_upwards [hK] with ω hω
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hx : a < RM ω
    · calc |gfun P u w RM ω| * |ramp a (1 / ((n : ℝ) + 1)) (RM ω)| ≤ K * 1 := by
            apply mul_le_mul (hω hx) _ (abs_nonneg _) hK0
            rw [abs_of_nonneg (ramp_nonneg _ _ _)]; exact ramp_le_one _ _ _
        _ = K := mul_one K
    · push Not at hx
      rw [ramp_of_le (by positivity) hx, abs_zero, mul_zero]
      exact hK0
  · have := (ramp_tendsto a (RM ω)).const_mul (gfun P u w RM ω)
    simpa [mul_comm] using this

lemma lim_mt (h : Ctx P u w mt RM) (a : ℝ) :
    Tendsto (fun n : ℕ => ∫ ω, mt ω * ramp a (1 / ((n : ℝ) + 1)) (RM ω) ∂P) atTop
      (𝓝 (∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * mt ω ∂P)) := by
  refine tendsto_integral_of_dominated_convergence (fun ω => |mt ω|) (fun n =>
    (int_mt_ramp h a _).aestronglyMeasurable) h.mt_int.abs
    (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
  · rw [Real.norm_eq_abs, abs_mul]
    calc |mt ω| * |ramp a (1 / ((n : ℝ) + 1)) (RM ω)| ≤ |mt ω| * 1 := by
          gcongr
          rw [abs_of_nonneg (ramp_nonneg _ _ _)]; exact ramp_le_one _ _ _
      _ = |mt ω| := mul_one _
  · have := (ramp_tendsto a (RM ω)).const_mul (mt ω)
    simpa [mul_comm] using this

/-- The cross identity for tails. -/
lemma cross_tail (h : Ctx P u w mt RM) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * gfun P u w RM ω ∂P) *
      (∫ ω, (Ioi b).indicator (fun _ => (1:ℝ)) (RM ω) * mt ω ∂P) =
    (∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * mt ω ∂P) *
      (∫ ω, (Ioi b).indicator (fun _ => (1:ℝ)) (RM ω) * gfun P u w RM ω ∂P) := by
  have l1 := (lim_g h ha).mul (lim_mt h b)
  have l2 := (lim_mt h a).mul (lim_g h hb)
  refine tendsto_nhds_unique l1 (l2.congr fun n => ?_)
  exact (cross_ramp h ha hb (by positivity)).symm


/-- Tail integrals of `g` and `mt` are proportional, with a positive constant. -/
lemma tail_lam (h : Ctx P u w mt RM) : ∃ lam : ℝ, 0 < lam ∧ ∀ a, 0 < a →
    (∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * gfun P u w RM ω ∂P) =
      lam * ∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * mt ω ∂P := by
  -- a level `b0 > 0` with `P(R_M > b0) > 0`
  have hex : ∃ b0 : ℝ, 0 < b0 ∧ 0 < P {ω | b0 < RM ω} := by
    by_contra hne
    push Not at hne
    have hz : ∀ n : ℕ, P {ω | 1 / ((n : ℝ) + 1) < RM ω} = 0 := fun n =>
      nonpos_iff_eq_zero.1 (hne _ (by positivity))
    have hU : {ω | 0 < RM ω} = ⋃ n : ℕ, {ω | 1 / ((n : ℝ) + 1) < RM ω} := by
      ext ω; simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · intro hω
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hω
        exact ⟨n, hn⟩
      · rintro ⟨n, hn⟩; exact lt_trans (by positivity) hn
    have h0 : P {ω | 0 < RM ω} = 0 := by
      rw [hU]; exact measure_iUnion_null hz
    have h1 : P {ω | 0 < RM ω}ᶜ = 0 := by
      have := h.pos; rw [ae_iff] at this
      rw [compl_setOf]; simpa [not_lt] using this
    have : P univ = 0 := by
      rw [← union_compl_self {ω | 0 < RM ω}]
      exact measure_union_null h0 h1
    simp at this
  obtain ⟨b0, hb0, hPb0⟩ := hex
  set Tg := fun a => ∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * gfun P u w RM ω ∂P
  set Tm := fun a => ∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * mt ω ∂P
  have hTm_nn : ∀ a, 0 ≤ᵐ[P] fun ω => (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * mt ω :=
    fun a => h.mt_pos.mono fun ω hω => mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      hω.le
  have hTg_nn : ∀ a, 0 ≤ᵐ[P] fun ω => (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) *
      gfun P u w RM ω :=
    fun a => (g_nonneg h).mono fun ω hω => mul_nonneg
      (indicator_nonneg (fun _ _ => zero_le_one) _) hω
  have hTm0 : 0 < Tm b0 := by
    rw [integral_pos_iff_support_of_nonneg_ae (hTm_nn b0) (int_mt_tail h b0)]
    refine lt_of_lt_of_le hPb0 (measure_mono_ae ?_)
    filter_upwards [h.mt_pos] with ω hω hmem
    replace hmem : b0 < RM ω := hmem
    show ω ∈ Function.support (fun ω => (Ioi b0).indicator (fun _ => (1:ℝ)) (RM ω) * mt ω)
    rw [Function.mem_support, indicator_of_mem (show RM ω ∈ Ioi b0 from hmem), one_mul]
    exact hω.ne'
  set lam := Tg b0 / Tm b0 with hlam
  have hrel : ∀ a, 0 < a → Tg a = lam * Tm a := by
    intro a ha
    have := cross_tail h ha hb0
    simp only [Tg, Tm] at this ⊢
    rw [hlam]
    field_simp
    linarith
  have hlam0 : 0 ≤ lam := div_nonneg (integral_nonneg_of_ae (hTg_nn b0)) hTm0.le
  refine ⟨lam, ?_, hrel⟩
  rcases hlam0.lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    -- then `g = 0` a.s., hence `Ψ = 0` a.s., contradicting `E[Ψ] = 1`
    have hg0 : ∀ n : ℕ, ∀ᵐ ω ∂P, (Ioi (1 / ((n : ℝ) + 1))).indicator (fun _ => (1:ℝ)) (RM ω) *
        gfun P u w RM ω = 0 := by
      intro n
      have hT : Tg (1 / ((n : ℝ) + 1)) = 0 := by rw [hrel _ (by positivity), ← hzero, zero_mul]
      exact (integral_eq_zero_iff_of_nonneg_ae (hTg_nn _) (int_g_tail h (by positivity))).1 hT
    have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, (Ioi (1 / ((n : ℝ) + 1))).indicator (fun _ => (1:ℝ)) (RM ω) *
        gfun P u w RM ω = 0 := ae_all_iff.2 hg0
    obtain ⟨-, -, hupos⟩ := u_props h.hu
    have hΨ0 : ∀ᵐ ω ∂P, deriv w (1 - cdf (P.map RM) (RM ω)) = 0 := by
      filter_upwards [hall, h.pos] with ω hω hp
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hp
      have := hω n
      rw [indicator_of_mem (show RM ω ∈ Ioi (1 / ((n : ℝ) + 1)) from hn), one_mul] at this
      unfold gfun at this
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 (hupos _ hp).ne'
      · exact h1
    have := h.psi_integral
    rw [integral_eq_zero_of_ae hΨ0] at this
    norm_num at this

end Ctx

end BCK


open MeasureTheory ProbabilityTheory Filter Topology Set BetaCoskew.ThreeMoment

namespace BCK

namespace Ctx

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {u w : ℝ → ℝ} {mt RM : Ω → ℝ}

/-- Evaluating the pushforward of a truncated density. -/
lemma eval_map (h : Ctx P u w mt RM) {a : ℝ} {f : Ω → ℝ} (hf0 : 0 ≤ᵐ[P] f)
    (hfi : Integrable (fun ω => (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f ω) P)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (P.withDensity (fun ω => ENNReal.ofReal ((Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f ω))).map
      RM S = ENNReal.ofReal (∫ ω, (S ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f ω ∂P) := by
  have hind : ∀ ω, (S ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f ω =
      S.indicator (fun _ => (1:ℝ)) (RM ω) * ((Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f ω) := by
    intro ω
    by_cases h1 : RM ω ∈ S <;> by_cases h2 : RM ω ∈ Ioi a <;>
      simp [indicator, h1, h2]
  have hint : Integrable (fun ω => (S ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f ω) P := by
    refine (hfi.bdd_mul (c := 1) (((measurable_const.indicator hS).comp
      h.RM_meas)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)).congr
      (Eventually.of_forall fun ω => (hind ω).symm)
    by_cases h1 : RM ω ∈ S
    · simp [indicator_of_mem h1]
    · simp [indicator_of_notMem h1]
  have hnn : 0 ≤ᵐ[P] fun ω => (S ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f ω :=
    hf0.mono fun ω hω => mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) hω
  rw [Measure.map_apply h.RM_meas hS, withDensity_apply _ (h.RM_meas hS),
    ofReal_integral_eq_lintegral_ofReal hint hnn, ← lintegral_indicator (h.RM_meas hS)]
  congr 1
  funext ω
  by_cases h1 : RM ω ∈ S
  · rw [indicator_of_mem (show ω ∈ RM ⁻¹' S from h1), hind ω, indicator_of_mem h1, one_mul]
  · rw [indicator_of_notMem (show ω ∉ RM ⁻¹' S from h1), hind ω, indicator_of_notMem h1,
      zero_mul, ENNReal.ofReal_zero]

/-- Borel extension of the tail identity. -/
lemma tail_set (h : Ctx P u w mt RM) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hrel : ∀ a, 0 < a →
      (∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * gfun P u w RM ω ∂P) =
        lam * ∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * mt ω ∂P)
    {a : ℝ} (ha : 0 < a) {B : Set ℝ} (hB : MeasurableSet B) :
    (∫ ω, (B ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * gfun P u w RM ω ∂P) =
      lam * ∫ ω, (B ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * mt ω ∂P := by
  set f1 : Ω → ℝ := gfun P u w RM with hf1
  set f2 : Ω → ℝ := fun ω => lam * mt ω with hf2
  have h10 : 0 ≤ᵐ[P] f1 := g_nonneg h
  have h20 : 0 ≤ᵐ[P] f2 := h.mt_pos.mono fun ω hω => mul_nonneg hlam0 hω.le
  have hi1 : ∀ c, 0 < c →
      Integrable (fun ω => (Ioi c).indicator (fun _ => (1:ℝ)) (RM ω) * f1 ω) P :=
    fun c hc => int_g_tail h hc
  have hi2 : ∀ c, Integrable (fun ω => (Ioi c).indicator (fun _ => (1:ℝ)) (RM ω) * f2 ω) P :=
    fun c => ((int_mt_tail h c).const_mul lam).congr (Eventually.of_forall fun ω => by
      simp only [hf2]; ring)
  have hrel' : ∀ c, 0 < c →
      (∫ ω, (Ioi c).indicator (fun _ => (1:ℝ)) (RM ω) * f1 ω ∂P) =
        ∫ ω, (Ioi c).indicator (fun _ => (1:ℝ)) (RM ω) * f2 ω ∂P := by
    intro c hc
    rw [hrel c hc, ← integral_const_mul]
    congr 1; funext ω; simp only [hf2]; ring
  -- the two truncated laws agree on all half-lines
  set ν1 := (P.withDensity (fun ω => ENNReal.ofReal
    ((Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f1 ω))).map RM
  set ν2 := (P.withDensity (fun ω => ENNReal.ofReal
    ((Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f2 ω))).map RM
  have e1 : ∀ S, MeasurableSet S → ν1 S =
      ENNReal.ofReal (∫ ω, (S ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f1 ω ∂P) :=
    fun S hS => eval_map h h10 (hi1 a ha) hS
  have e2 : ∀ S, MeasurableSet S → ν2 S =
      ENNReal.ofReal (∫ ω, (S ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f2 ω ∂P) :=
    fun S hS => eval_map h h20 (hi2 a) hS
  have hfin : IsFiniteMeasure ν1 := ⟨by rw [e1 univ MeasurableSet.univ]; exact ENNReal.ofReal_lt_top⟩
  have hsplit : ∀ (f : Ω → ℝ) (t : ℝ),
      Integrable (fun ω => (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f ω) P →
      Integrable (fun ω => (Ioi (max a t)).indicator (fun _ => (1:ℝ)) (RM ω) * f ω) P →
      (∫ ω, (Iic t ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f ω ∂P) =
        (∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f ω ∂P) -
          ∫ ω, (Ioi (max a t)).indicator (fun _ => (1:ℝ)) (RM ω) * f ω ∂P := by
    intro f t hA hB
    rw [← integral_sub hA hB]
    congr 1; funext ω
    by_cases h1 : RM ω ≤ t <;> by_cases h2 : a < RM ω
    · have : ¬ max a t < RM ω := by
        rw [max_lt_iff]; push Not; intro _; exact h1
      simp [indicator, h1, h2, this]
    · have : ¬ max a t < RM ω := by
        rw [max_lt_iff]; push Not; intro h; exact absurd h h2
      simp [indicator, h1, h2, this]
    · have : max a t < RM ω := by
        rw [max_lt_iff]; exact ⟨h2, by push Not at h1; exact h1⟩
      simp [indicator, h1, h2, this]
    · have : ¬ max a t < RM ω := by
        rw [max_lt_iff]; push Not; intro h; exact absurd h h2
      simp [indicator, h1, h2, this]
  have hIic : ∀ t, ν1 (Iic t) = ν2 (Iic t) := by
    intro t
    rw [e1 _ measurableSet_Iic, e2 _ measurableSet_Iic,
      hsplit f1 t (hi1 a ha) (hi1 _ (lt_of_lt_of_le ha (le_max_left _ _))),
      hsplit f2 t (hi2 a) (hi2 _),
      hrel' a ha, hrel' _ (lt_of_lt_of_le ha (le_max_left _ _))]
  have hν : ν1 = ν2 := Measure.ext_of_Iic ν1 ν2 hIic
  have hB1 := e1 B hB
  rw [hν, e2 B hB] at hB1
  have n1 : 0 ≤ ∫ ω, (B ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f1 ω ∂P :=
    integral_nonneg_of_ae (h10.mono fun ω hω => mul_nonneg
      (indicator_nonneg (fun _ _ => zero_le_one) _) hω)
  have n2 : 0 ≤ ∫ ω, (B ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * f2 ω ∂P :=
    integral_nonneg_of_ae (h20.mono fun ω hω => mul_nonneg
      (indicator_nonneg (fun _ _ => zero_le_one) _) hω)
  have := (ENNReal.ofReal_eq_ofReal_iff n2 n1).1 hB1
  rw [← this, ← integral_const_mul]
  congr 1; funext ω; simp only [hf2]; ring

end Ctx

end BCK


open MeasureTheory ProbabilityTheory Filter Topology Set

namespace BCK

/-- Probability integral transform for `0 ≤ t ≤ 1`. -/
lemma measure_cdf_le' (μ : Measure ℝ) [IsProbabilityMeasure μ] (hF : Continuous (cdf μ))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    μ {x | cdf μ x ≤ t} = ENNReal.ofReal t := by
  rcases ht1.lt_or_eq with h | h
  · exact measure_cdf_le μ hF ht0 h
  · have : {x | cdf μ x ≤ t} = univ := by
      ext x; simp only [mem_setOf_eq, mem_univ, iff_true]; rw [h]; exact cdf_le_one μ x
    rw [this, measure_univ, h, ENNReal.ofReal_one]

/-- For a continuous cdf, `F(X) ∈ (0,1)` almost surely. -/
lemma cdf_mem_Ioo_ae (μ : Measure ℝ) [IsProbabilityMeasure μ] (hF : Continuous (cdf μ)) :
    ∀ᵐ x ∂μ, cdf μ x ∈ Ioo (0:ℝ) 1 := by
  have h0 : μ {x | cdf μ x ≤ 0} = 0 := by
    rw [measure_cdf_le μ hF le_rfl zero_lt_one, ENNReal.ofReal_zero]
  have h1 : μ {x | 1 ≤ cdf μ x} = 0 := by
    -- `{F ≥ 1}` is the complement of `⋃ {F ≤ 1 - 1/(n+2)}`
    have hU : {x | cdf μ x < 1} = ⋃ n : ℕ, {x | cdf μ x ≤ 1 - 1 / ((n : ℝ) + 2)} := by
      ext x; simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
        refine ⟨n, ?_⟩
        have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith
      · rintro ⟨n, hn⟩
        have : 0 < 1 / ((n : ℝ) + 2) := by positivity
        linarith
    have hmono : Monotone (fun n : ℕ => {x | cdf μ x ≤ 1 - 1 / ((n : ℝ) + 2)}) := by
      intro n m hnm x hx
      simp only [mem_setOf_eq] at hx ⊢
      have : 1 / ((m : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) :=
        one_div_le_one_div_of_le (by positivity) (by
          have : (n : ℝ) ≤ m := by exact_mod_cast hnm
          linarith)
      linarith
    have hlim := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [← hU] at hlim
    have hval : ∀ n : ℕ, μ {x | cdf μ x ≤ 1 - 1 / ((n : ℝ) + 2)} =
        ENNReal.ofReal (1 - 1 / ((n : ℝ) + 2)) := by
      intro n
      apply measure_cdf_le μ hF
      · have : 1 / ((n : ℝ) + 2) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        linarith
      · have : 0 < 1 / ((n : ℝ) + 2) := by positivity
        linarith
    replace hlim := hlim.congr (fun n => by simp only [Function.comp_apply]; exact hval n)
    have hlim2 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 - 1 / ((n : ℝ) + 2))) atTop
        (𝓝 (ENNReal.ofReal 1)) := by
      apply ENNReal.tendsto_ofReal
      have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        refine squeeze_zero (fun n => by positivity) (fun n => ?_) this
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub this
    have hlt : μ {x | cdf μ x < 1} = 1 := by
      rw [tendsto_nhds_unique hlim hlim2, ENNReal.ofReal_one]
    have hcompl : {x | 1 ≤ cdf μ x} = {x | cdf μ x < 1}ᶜ := by
      ext x; simp [not_lt]
    rw [hcompl, measure_compl (measurableSet_lt (cdf μ).mono.measurable measurable_const)
      (measure_ne_top _ _), hlt, measure_univ, tsub_self]
  have hA : ∀ᵐ x ∂μ, ¬ cdf μ x ≤ 0 := by
    rw [ae_iff]; simpa using h0
  have hB : ∀ᵐ x ∂μ, ¬ 1 ≤ cdf μ x := by
    rw [ae_iff]; simpa using h1
  filter_upwards [hA, hB] with x h1 h2
  exact ⟨lt_of_not_ge h1, lt_of_not_ge h2⟩

/-- A bounded quantile function on `[lo, hi]`. -/
noncomputable def qB (μ : Measure ℝ) (lo hi s : ℝ) : ℝ :=
  sInf {x | x ∈ Icc lo hi ∧ min s 1 ≤ cdf μ x}

section qB

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] {lo hi : ℝ}

lemma qB_set_ne (hle : lo ≤ hi) (hhi : cdf μ hi = 1) (s : ℝ) :
    ({x | x ∈ Icc lo hi ∧ min s 1 ≤ cdf μ x} : Set ℝ).Nonempty :=
  ⟨hi, ⟨⟨hle, le_rfl⟩, by rw [hhi]; exact min_le_right _ _⟩⟩

lemma qB_set_bdd (s : ℝ) : BddBelow ({x | x ∈ Icc lo hi ∧ min s 1 ≤ cdf μ x} : Set ℝ) :=
  ⟨lo, fun _ hx => hx.1.1⟩

lemma qB_mono (hle : lo ≤ hi) (hhi : cdf μ hi = 1) : Monotone (qB μ lo hi) := by
  intro s s' hss
  apply csInf_le_csInf (qB_set_bdd μ s) (qB_set_ne μ hle hhi s')
  intro x hx
  exact ⟨hx.1, le_trans (min_le_min_right 1 hss) hx.2⟩

lemma qB_measurable (hle : lo ≤ hi) (hhi : cdf μ hi = 1) : Measurable (qB μ lo hi) :=
  (qB_mono μ hle hhi).measurable

lemma qB_mem (hle : lo ≤ hi) (hhi : cdf μ hi = 1) (s : ℝ) : qB μ lo hi s ∈ Icc lo hi := by
  have hc : IsClosed (Icc lo hi) := isClosed_Icc
  refine ⟨le_csInf (qB_set_ne μ hle hhi s) fun x hx => hx.1.1, ?_⟩
  exact csInf_le (qB_set_bdd μ s) ⟨⟨hle, le_rfl⟩, by rw [hhi]; exact min_le_right _ _⟩

lemma qB_le_iff (hF : Continuous (cdf μ)) (hle : lo ≤ hi) (hhi : cdf μ hi = 1)
    (hlo : cdf μ lo = 0) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (x : ℝ) :
    qB μ lo hi s ≤ x ↔ s ≤ cdf μ x := by
  have hmin : min s 1 = s := min_eq_left hs1
  set T := {x | x ∈ Icc lo hi ∧ min s 1 ≤ cdf μ x} with hT
  have hclosed : IsClosed T := by
    have : T = Icc lo hi ∩ {x | min s 1 ≤ cdf μ x} := rfl
    rw [this]; exact isClosed_Icc.inter (isClosed_le continuous_const hF)
  have hmem : qB μ lo hi s ∈ T := hclosed.csInf_mem (qB_set_ne μ hle hhi s) (qB_set_bdd μ s)
  constructor
  · intro hq
    have := hmem.2
    rw [hmin] at this
    exact le_trans this ((cdf μ).mono hq)
  · intro hx
    by_cases hxhi : hi ≤ x
    · exact le_trans (qB_mem μ hle hhi s).2 hxhi
    · push Not at hxhi
      by_cases hxlo : x < lo
      · exfalso
        have : cdf μ x ≤ cdf μ lo := (cdf μ).mono hxlo.le
        rw [hlo] at this; linarith
      · push Not at hxlo
        exact csInf_le (qB_set_bdd μ s) ⟨⟨hxlo, hxhi.le⟩, by rw [hmin]; exact hx⟩

/-- Quantile coupling: `qB μ₂ ∘ F₁` pushes `μ₁` to `μ₂`. -/
lemma map_qB_cdf (μ1 : Measure ℝ) [IsProbabilityMeasure μ1] (hF1 : Continuous (cdf μ1))
    (hF : Continuous (cdf μ)) (hle : lo ≤ hi) (hhi : cdf μ hi = 1) (hlo : cdf μ lo = 0) :
    μ1.map (fun y => qB μ lo hi (cdf μ1 y)) = μ := by
  have hm : Measurable (fun y => qB μ lo hi (cdf μ1 y)) :=
    (qB_measurable μ hle hhi).comp (cdf μ1).mono.measurable
  haveI : IsFiniteMeasure (μ1.map (fun y => qB μ lo hi (cdf μ1 y))) :=
    Measure.isFiniteMeasure_map _ _
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply hm measurableSet_Iic, ← ofReal_cdf μ x]
  have hae : (fun y => qB μ lo hi (cdf μ1 y)) ⁻¹' Iic x =ᵐ[μ1] {y | cdf μ1 y ≤ cdf μ x} := by
    filter_upwards [cdf_mem_Ioo_ae μ1 hF1] with y hy
    apply propext
    exact qB_le_iff μ hF hle hhi hlo hy.1 hy.2.le x
  rw [measure_congr hae, measure_cdf_le' μ1 hF1 (cdf_nonneg μ x) (cdf_le_one μ x)]

end qB

end BCK


open MeasureTheory ProbabilityTheory Filter Topology Set BetaCoskew.ThreeMoment

namespace BCK

section Cond

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {RM : Ω → ℝ}

lemma condLaw_prob (hRM : Measurable RM) {A : Set Ω} (hA0 : P A ≠ 0) :
    IsProbabilityMeasure ((P[|A]).map RM) := by
  haveI := cond_isProbabilityMeasure (μ := P) hA0
  exact Measure.isProbabilityMeasure_map hRM.aemeasurable

lemma condLaw_cont (hRM : Measurable RM) (hna : ∀ c, P {ω | RM ω = c} = 0) {A : Set Ω}
    (hA : MeasurableSet A) (hA0 : P A ≠ 0) : Continuous (cdf ((P[|A]).map RM)) := by
  haveI := condLaw_prob hRM hA0
  rw [cdf_continuous_iff]
  intro c
  rw [Measure.map_apply hRM (measurableSet_singleton c), cond_apply hA]
  have : P (A ∩ RM ⁻¹' {c}) = 0 := measure_mono_null inter_subset_right (by
    have := hna c
    rwa [show {ω | RM ω = c} = RM ⁻¹' {c} from rfl] at this)
  rw [this, mul_zero]

lemma condLaw_cdf_one (hRM : Measurable RM) {A : Set Ω} (hA : MeasurableSet A) (hA0 : P A ≠ 0)
    {hi : ℝ} (h : ∀ ω ∈ A, RM ω ≤ hi) : cdf ((P[|A]).map RM) hi = 1 := by
  haveI := condLaw_prob hRM hA0
  rw [cdf_eq_real, measureReal_def, Measure.map_apply hRM measurableSet_Iic, cond_apply hA]
  have : A ∩ RM ⁻¹' Iic hi = A := inter_eq_left.2 (fun ω hω => h ω hω)
  rw [this, ENNReal.inv_mul_cancel hA0 (measure_ne_top _ _), ENNReal.toReal_one]

lemma condLaw_cdf_zero (hRM : Measurable RM) {A : Set Ω} (hA : MeasurableSet A) (hA0 : P A ≠ 0)
    {lo : ℝ} (h : ∀ ω ∈ A, lo < RM ω) : cdf ((P[|A]).map RM) lo = 0 := by
  haveI := condLaw_prob hRM hA0
  rw [cdf_eq_real, measureReal_def, Measure.map_apply hRM measurableSet_Iic, cond_apply hA]
  have : A ∩ RM ⁻¹' Iic lo = ∅ := by
    ext ω; simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_empty_iff_false, iff_false,
      not_and, not_le]
    exact fun hω => h ω hω
  rw [this, measure_empty, mul_zero, ENNReal.toReal_zero]

lemma inter_eq_condLaw {A : Set Ω} (hRM : Measurable RM) (hA : MeasurableSet A) {S : Set ℝ}
    (hS : MeasurableSet S) : P (A ∩ RM ⁻¹' S) = (P[|A]).map RM S * P A := by
  rw [Measure.map_apply hRM hS, cond_mul_eq_inter hA]

/-- Shrinking a set to any smaller mass using the conditional rank of `RM`. -/
lemma shrink (hRM : Measurable RM) (hna : ∀ c, P {ω | RM ω = c} = 0) {A : Set Ω}
    (hA : MeasurableSet A) (hA0 : P A ≠ 0) {m : ENNReal} (hmA : m ≤ P A) :
    ∃ A' ⊆ A, MeasurableSet A' ∧ P A' = m := by
  haveI := condLaw_prob hRM hA0
  set μA := (P[|A]).map RM
  have hcont := condLaw_cont hRM hna hA hA0
  have hfin : P A ≠ ⊤ := measure_ne_top _ _
  set t := (m / P A).toReal with ht
  have hle1 : m / P A ≤ 1 := ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hmA)
  have hne : m / P A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hle1
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have ht1 : t ≤ 1 := by
    rw [ht]; exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hle1)
  set S : Set ℝ := {x | cdf μA x ≤ t}
  have hS : MeasurableSet S := measurableSet_le (cdf μA).mono.measurable measurable_const
  refine ⟨A ∩ RM ⁻¹' S, inter_subset_left, hA.inter (hRM hS), ?_⟩
  rw [inter_eq_condLaw hRM hA hS, measure_cdf_le' μA hcont ht0 ht1, ht,
    ENNReal.ofReal_toReal hne, ENNReal.div_mul_cancel hA0 hfin]

/-- Transfer of a conditional-law identity to the original measure. -/
lemma inter_eq_of_condLaw_eq {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hmass : P A = P B) {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hlaw : (P[|A]).map f = (P[|B]).map g) {S : Set ℝ} (hS : MeasurableSet S) :
    P (A ∩ f ⁻¹' S) = P (B ∩ g ⁻¹' S) := by
  rw [← cond_mul_eq_inter hA, ← cond_mul_eq_inter hB, ← Measure.map_apply hf hS,
    ← Measure.map_apply hg hS, hlaw, hmass]

/-- Set integrals through the conditional law. -/
lemma setIntegral_eq_condLaw {A : Set Ω} (hA0 : P A ≠ 0) {f : Ω → ℝ} (hf : Measurable f) :
    ∫ ω in A, f ω ∂P = (P A).toReal * ∫ x, x ∂((P[|A]).map f) := by
  have hrestr : P.restrict A = P A • P[|A] := by
    rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel hA0 (measure_ne_top _ _),
      one_smul]
  rw [hrestr, integral_smul_measure, smul_eq_mul,
    integral_map (μ := P[|A]) hf.aemeasurable (f := fun x : ℝ => x) aestronglyMeasurable_id]

end Cond

end BCK


open MeasureTheory ProbabilityTheory Filter Topology Set BetaCoskew.ThreeMoment

namespace BCK

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma law_preimage {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hlaw : P.map X = P.map Y) {E : Set ℝ} (hE : MeasurableSet E) :
    P (X ⁻¹' E) = P (Y ⁻¹' E) := by
  rw [← Measure.map_apply hX hE, ← Measure.map_apply hY hE, hlaw]

lemma law_ae {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hlaw : P.map X = P.map Y) {E : Set ℝ} (hE : MeasurableSet E)
    (hYE : ∀ᵐ ω ∂P, Y ω ∈ E) : ∀ᵐ ω ∂P, X ω ∈ E := by
  have h1 : ∀ᵐ x ∂(P.map Y), x ∈ E := (ae_map_iff hY.aemeasurable hE).2 hYE
  rw [← hlaw] at h1
  exact (ae_map_iff hX.aemeasurable hE).1 h1

lemma law_integral {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hlaw : P.map X = P.map Y) {G : ℝ → ℝ} (hG : AEStronglyMeasurable G (P.map Y)) :
    ∫ ω, G (X ω) ∂P = ∫ ω, G (Y ω) ∂P := by
  rw [← integral_map hX.aemeasurable (hlaw ▸ hG), hlaw, integral_map hY.aemeasurable hG]

lemma law_integrable {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hlaw : P.map X = P.map Y) {G : ℝ → ℝ} (hG : AEStronglyMeasurable G (P.map Y))
    (hint : Integrable (fun ω => G (Y ω)) P) : Integrable (fun ω => G (X ω)) P := by
  have h1 : Integrable G (P.map Y) := (integrable_map_measure hG hY.aemeasurable).2 hint
  rw [← hlaw] at h1 hG
  exact (integrable_map_measure hG hX.aemeasurable).1 h1

end Law

namespace Ctx

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {u w : ℝ → ℝ} {mt RM : Ω → ℝ}

lemma G_aesm (h : Ctx P u w mt RM) :
    AEStronglyMeasurable (fun x => u x * deriv w (1 - cdf (P.map RM) x)) (P.map RM) := by
  have hrestr : (P.map RM).restrict (Ioi 0) = P.map RM := by
    apply Measure.restrict_eq_self_of_ae_mem
    exact (ae_map_iff h.RM_meas.aemeasurable measurableSet_Ioi).2 h.pos
  have h1 : AEStronglyMeasurable u (P.map RM) := by
    rw [← hrestr]; exact h.u_cont.aestronglyMeasurable measurableSet_Ioi
  have h2 : Measurable (fun x => deriv w (1 - cdf (P.map RM) x)) :=
    (measurable_deriv w).comp (measurable_const.sub (cdf (P.map RM)).mono.measurable)
  exact h1.mul h2.aestronglyMeasurable

/-- A level `c > 0` above which the rank weight is positive with positive probability. -/
lemma exists_level (h : Ctx P u w mt RM) : ∃ c : ℝ, 0 < c ∧
    0 < P {ω | c < RM ω ∧ 0 < deriv w (1 - cdf (P.map RM) (RM ω))} := by
  obtain ⟨C, hC⟩ := h.psi_bdd
  set Ψ := fun ω => deriv w (1 - cdf (P.map RM) (RM ω))
  have hpos : 0 < P {ω | 0 < Ψ ω} := by
    by_contra hz
    push Not at hz
    have hz' : P {ω | 0 < Ψ ω} = 0 := nonpos_iff_eq_zero.1 hz
    have hae : Ψ =ᵐ[P] 0 := by
      have : ∀ᵐ ω ∂P, ¬ 0 < Ψ ω := by rw [ae_iff]; simpa using hz'
      filter_upwards [this, hC] with ω h1 h2
      exact le_antisymm (not_lt.1 h1) h2.1
    have := h.psi_integral
    rw [integral_eq_zero_of_ae hae] at this
    norm_num at this
  by_contra hne
  push Not at hne
  have hz : ∀ n : ℕ, P {ω | 1 / ((n : ℝ) + 1) < RM ω ∧ 0 < Ψ ω} = 0 := fun n =>
    nonpos_iff_eq_zero.1 (hne _ (by positivity))
  have hsub : {ω | 0 < Ψ ω} ⊆ (⋃ n : ℕ, {ω | 1 / ((n : ℝ) + 1) < RM ω ∧ 0 < Ψ ω}) ∪
      {ω | RM ω ≤ 0} := by
    intro ω hω
    by_cases hr : 0 < RM ω
    · left
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
      exact mem_iUnion.2 ⟨n, hn, hω⟩
    · right; exact not_lt.1 hr
  have hnull : P {ω | RM ω ≤ 0} = 0 := by
    have := h.pos; rw [ae_iff] at this; simpa [not_lt] using this
  have := measure_mono_null hsub (measure_union_null (measure_iUnion_null hz) hnull)
  rw [this] at hpos
  exact lt_irrefl _ hpos

/-- A payoff with the market's law but strictly smaller cost contradicts equilibrium. -/
lemma improve (h : Ctx P u w mt RM) {X : Ω → ℝ} (hXm : Measurable X)
    (hlaw : P.map X = P.map RM) (hint : Integrable (fun ω => mt ω * X ω) P)
    (hcost : ∫ ω, mt ω * X ω ∂P < 1) : False := by
  obtain ⟨hd, hanti, hupos⟩ := u_props h.hu
  set F := cdf (P.map RM) with hF
  have hFX : cdf (P.map X) = F := by rw [hlaw]
  have hFm : Measurable F := F.mono.measurable
  have hψm : Measurable (fun x => deriv w (1 - F x)) :=
    (measurable_deriv w).comp (measurable_const.sub hFm)
  have hXpos : ∀ᵐ ω ∂P, 0 < X ω := law_ae hXm h.RM_meas hlaw measurableSet_Ioi h.pos
  obtain ⟨C, hC⟩ := h.psi_bdd
  have hCX : ∀ᵐ ω ∂P, 0 ≤ deriv w (1 - F (X ω)) ∧ deriv w (1 - F (X ω)) ≤ C := by
    have hE : MeasurableSet {x : ℝ | 0 ≤ deriv w (1 - F x) ∧ deriv w (1 - F x) ≤ C} :=
      (measurableSet_le measurable_const hψm).inter (measurableSet_le hψm measurable_const)
    exact law_ae hXm h.RM_meas hlaw hE hC
  obtain ⟨c, hc, hPc⟩ := exists_level h
  have hPcX : 0 < P {ω | c < X ω ∧ 0 < deriv w (1 - F (X ω))} := by
    have hE : MeasurableSet {x : ℝ | c < x ∧ 0 < deriv w (1 - F x)} :=
      measurableSet_Ioi.inter (measurableSet_lt measurable_const hψm)
    have := law_preimage hXm h.RM_meas hlaw hE
    simp only [preimage_setOf_eq] at this
    rw [this]; exact hPc
  -- the shift
  set ind : ℝ → ℝ := (Ioi c).indicator (fun _ => (1:ℝ)) with hind
  have hindm : Measurable ind := measurable_const.indicator measurableSet_Ioi
  have hmtind : Integrable (fun ω => mt ω * ind (X ω)) P := by
    refine h.mt_int.mul_bdd (c := 1) (hindm.comp hXm).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_) |>.congr (Eventually.of_forall fun ω => by
        simp [mul_comm])
    simp only [Function.comp_apply, hind, Real.norm_eq_abs]
    by_cases hx : X ω ∈ Ioi c
    · rw [indicator_of_mem hx]; simp
    · rw [indicator_of_notMem hx]; simp
  have hden : 0 < ∫ ω, mt ω * ind (X ω) ∂P := by
    have hnn : 0 ≤ᵐ[P] fun ω => mt ω * ind (X ω) := h.mt_pos.mono fun ω hω =>
      mul_nonneg hω.le (indicator_nonneg (fun _ _ => zero_le_one) _)
    rw [integral_pos_iff_support_of_nonneg_ae hnn hmtind]
    refine lt_of_lt_of_le hPcX (measure_mono_ae ?_)
    filter_upwards [h.mt_pos] with ω hω hmem
    replace hmem : c < X ω ∧ 0 < deriv w (1 - F (X ω)) := hmem
    show ω ∈ Function.support (fun ω => mt ω * ind (X ω))
    rw [Function.mem_support, hind, indicator_of_mem (show X ω ∈ Ioi c from hmem.1), mul_one]
    exact hω.ne'
  set ε := (1 - ∫ ω, mt ω * X ω ∂P) / ∫ ω, mt ω * ind (X ω) ∂P with hε
  have hεpos : 0 < ε := div_pos (by linarith) hden
  set φ : ℝ → ℝ := fun x => x + ε * ind x with hφ
  have hindmono : Monotone ind := by
    intro x y hxy
    simp only [hind]
    by_cases hx : x ∈ Ioi c
    · rw [indicator_of_mem hx, indicator_of_mem (show y ∈ Ioi c from lt_of_lt_of_le hx hxy)]
    · rw [indicator_of_notMem hx]; exact indicator_nonneg (fun _ _ => zero_le_one) _
  have hφmono : StrictMono φ := by
    intro x y hxy
    have := hindmono hxy.le
    simp only [hφ]; nlinarith
  have hφm : Measurable φ := measurable_id.add (measurable_const.mul hindm)
  have hYm : Measurable (fun ω => φ (X ω)) := hφm.comp hXm
  have hYpos : ∀ᵐ ω ∂P, 0 < φ (X ω) := hXpos.mono fun ω hω => by
    simp only [hφ]
    have := indicator_nonneg (s := Ioi c) (fun _ _ => zero_le_one (α := ℝ)) (X ω)
    nlinarith
  have hXna : ∀ c', P.map X {c'} = 0 := by rw [hlaw]; exact h.noAtoms
  have hYna := noAtoms_map_comp P hXm.aemeasurable hφmono hφm hXna
  have hYint : Integrable (fun ω => mt ω * φ (X ω)) P := by
    refine (hint.add (hmtind.const_mul ε)).congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, hφ]; ring
  have hYbud : ∫ ω, mt ω * φ (X ω) ∂P = 1 := by
    have e : (fun ω => mt ω * φ (X ω)) = fun ω => mt ω * X ω + ε * (mt ω * ind (X ω)) := by
      funext ω; simp only [hφ]; ring
    rw [e, integral_add hint (hmtind.const_mul ε), integral_const_mul, hε]
    field_simp
    ring
  have hcdfY : ∀ ω, cdf (P.map (fun ω => φ (X ω))) (φ (X ω)) = F (X ω) := by
    intro ω; rw [cdf_map_comp P hXm.aemeasurable hφmono hφm, hFX]
  -- integrability of the comparator objectives
  have hGX : Integrable (fun ω => u (X ω) * deriv w (1 - F (X ω))) P :=
    law_integrable hXm h.RM_meas hlaw (G := fun x => u x * deriv w (1 - F x)) h.G_aesm
      h.rdu_int
  have hdiffb : ∀ᵐ ω ∂P, 0 ≤ (u (φ (X ω)) - u (X ω)) * deriv w (1 - F (X ω)) ∧
      (u (φ (X ω)) - u (X ω)) * deriv w (1 - F (X ω)) ≤ deriv u c * ε * C := by
    filter_upwards [hXpos, hCX] with ω hω hψ
    have hC0 : 0 ≤ C := le_trans hψ.1 hψ.2
    by_cases hx : X ω ∈ Ioi c
    · have hφx : φ (X ω) = X ω + ε := by simp only [hφ, hind, indicator_of_mem hx, mul_one]
      rw [hφx]
      have hlt : u (X ω) < u (X ω + ε) := h.hu.strictMonoOn (show X ω ∈ Ioi (0:ℝ) from hω)
        (show X ω + ε ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; linarith) (by linarith)
      have hl := h.u_lip hc (x := X ω) (y := X ω + ε) (le_of_lt hx) (by
        have : c < X ω := hx; linarith)
      rw [add_sub_cancel_left, abs_of_pos hεpos, abs_of_pos (by linarith)] at hl
      refine ⟨mul_nonneg (by linarith) hψ.1, ?_⟩
      calc (u (X ω + ε) - u (X ω)) * deriv w (1 - F (X ω)) ≤ (deriv u c * ε) * C :=
            mul_le_mul hl hψ.2 hψ.1 (by have := hupos c hc; positivity)
        _ = deriv u c * ε * C := by ring
    · have hφx : φ (X ω) = X ω := by simp only [hφ, hind, indicator_of_notMem hx, mul_zero,
        add_zero]
      rw [hφx, sub_self, zero_mul]
      exact ⟨le_rfl, by have := hupos c hc; positivity⟩
  have hDmeas : AEStronglyMeasurable
      (fun ω => (u (φ (X ω)) - u (X ω)) * deriv w (1 - F (X ω))) P :=
    ((h.aesm_u hYm hYpos).sub (h.aesm_u hXm hXpos)).mul (hψm.comp hXm).aestronglyMeasurable
  have hDint : Integrable (fun ω => (u (φ (X ω)) - u (X ω)) * deriv w (1 - F (X ω))) P := by
    refine Integrable.of_bound (C := deriv u c * ε * C) hDmeas ?_
    filter_upwards [hdiffb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg hω.1]; exact hω.2
  have hYrdu : Integrable (fun ω => u (φ (X ω)) * deriv w (1 - F (X ω))) P :=
    (hDint.add hGX).congr (Eventually.of_forall fun ω => by simp only [Pi.add_apply]; ring)
  have hadm := h.adm hYm hYpos hYna hYint hYbud (by
    refine hYrdu.congr (Eventually.of_forall fun ω => ?_)
    simp only [hcdfY ω])
  simp only [hcdfY] at hadm
  -- strict improvement
  have hDpos : 0 < ∫ ω, (u (φ (X ω)) - u (X ω)) * deriv w (1 - F (X ω)) ∂P := by
    rw [integral_pos_iff_support_of_nonneg_ae (hdiffb.mono fun ω hω => hω.1) hDint]
    refine lt_of_lt_of_le hPcX (measure_mono_ae ?_)
    filter_upwards [hXpos] with ω hω hmem
    replace hmem : c < X ω ∧ 0 < deriv w (1 - F (X ω)) := hmem
    show ω ∈ Function.support (fun ω => (u (φ (X ω)) - u (X ω)) * deriv w (1 - F (X ω)))
    rw [Function.mem_support]
    have hφx : φ (X ω) = X ω + ε := by
      simp only [hφ, hind, indicator_of_mem (show X ω ∈ Ioi c from hmem.1), mul_one]
    rw [hφx]
    have hlt : u (X ω) < u (X ω + ε) := h.hu.strictMonoOn (show X ω ∈ Ioi (0:ℝ) from hω)
      (show X ω + ε ∈ Ioi (0:ℝ) by simp only [mem_Ioi]; linarith) (by linarith)
    exact mul_ne_zero (by linarith) hmem.2.ne'
  have hsplit : ∫ ω, u (φ (X ω)) * deriv w (1 - F (X ω)) ∂P =
      (∫ ω, (u (φ (X ω)) - u (X ω)) * deriv w (1 - F (X ω)) ∂P) +
        ∫ ω, u (X ω) * deriv w (1 - F (X ω)) ∂P := by
    rw [← integral_add hDint hGX]; congr 1; funext ω; ring
  have hsame : ∫ ω, u (X ω) * deriv w (1 - F (X ω)) ∂P =
      ∫ ω, u (RM ω) * deriv w (1 - F (RM ω)) ∂P :=
    law_integral hXm h.RM_meas hlaw (G := fun x => u x * deriv w (1 - F x)) h.G_aesm
  linarith

end Ctx

end BCK


open MeasureTheory ProbabilityTheory Filter Topology Set BetaCoskew.ThreeMoment

namespace BCK

lemma intOn_of_bdd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {A : Set Ω} (hA : MeasurableSet A) {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) {C : ℝ}
    (hb : ∀ ω ∈ A, |f ω| ≤ C) : IntegrableOn f A P := by
  refine Integrable.of_bound (C := C) hf.restrict ?_
  refine (ae_restrict_iff' hA).2 (Eventually.of_forall fun ω hω => ?_)
  rw [Real.norm_eq_abs]; exact hb ω hω

namespace Ctx

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {u w : ℝ → ℝ} {mt RM : Ω → ℝ}

/-- Anti-comonotonicity of the kernel and the market return. -/
lemma anti (h : Ctx P u w mt RM) (q0 q1 q2 q3 : ℝ) :
    P {ω | q0 < RM ω ∧ RM ω < q1 ∧ mt ω < q2} = 0 ∨
      P {ω | q1 < RM ω ∧ RM ω < q3 ∧ q2 < mt ω} = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA0, hB0⟩ := hcon
  set A0 := {ω | q0 < RM ω ∧ RM ω < q1 ∧ mt ω < q2} with hA0def
  set B0 := {ω | q1 < RM ω ∧ RM ω < q3 ∧ q2 < mt ω} with hB0def
  have hA0m : MeasurableSet A0 := (measurableSet_lt measurable_const h.RM_meas).inter
    ((measurableSet_lt h.RM_meas measurable_const).inter
      (measurableSet_lt h.mt_meas measurable_const))
  have hB0m : MeasurableSet B0 := (measurableSet_lt measurable_const h.RM_meas).inter
    ((measurableSet_lt h.RM_meas measurable_const).inter
      (measurableSet_lt measurable_const h.mt_meas))
  set m := min (P A0) (P B0) with hmdef
  have hm0 : m ≠ 0 := by
    rcases le_total (P A0) (P B0) with hle | hle
    · rw [hmdef, min_eq_left hle]; exact hA0
    · rw [hmdef, min_eq_right hle]; exact hB0
  obtain ⟨A, hAsub, hAm, hPA⟩ := shrink h.RM_meas h.noAtoms' hA0m hA0 (min_le_left _ _)
  obtain ⟨B, hBsub, hBm, hPB⟩ := shrink h.RM_meas h.noAtoms' hB0m hB0 (min_le_right _ _)
  have hPA0 : P A ≠ 0 := by rw [hPA]; exact hm0
  have hPB0 : P B ≠ 0 := by rw [hPB]; exact hm0
  have hmass : P A = P B := hPA.trans hPB.symm
  have hAr : ∀ ω ∈ A, q0 < RM ω ∧ RM ω < q1 ∧ mt ω < q2 := fun ω hω => hAsub hω
  have hBr : ∀ ω ∈ B, q1 < RM ω ∧ RM ω < q3 ∧ q2 < mt ω := fun ω hω => hBsub hω
  have hdisj : Disjoint A B := Set.disjoint_left.2 fun ω ha hb => by
    linarith [(hAr ω ha).2.1, (hBr ω hb).1]
  obtain ⟨ωa, hωa⟩ := nonempty_of_measure_ne_zero hPA0
  obtain ⟨ωb, hωb⟩ := nonempty_of_measure_ne_zero hPB0
  have hq01 : q0 ≤ q1 := by linarith [(hAr ωa hωa).1, (hAr ωa hωa).2.1]
  have hq13 : q1 ≤ q3 := by linarith [(hBr ωb hωb).1, (hBr ωb hωb).2.1]
  -- conditional laws
  set μ1 := (P[|A]).map RM with hμ1
  set μ2 := (P[|B]).map RM with hμ2
  haveI := condLaw_prob h.RM_meas hPA0
  haveI := condLaw_prob h.RM_meas hPB0
  have hc1 : Continuous (cdf μ1) := condLaw_cont h.RM_meas h.noAtoms' hAm hPA0
  have hc2 : Continuous (cdf μ2) := condLaw_cont h.RM_meas h.noAtoms' hBm hPB0
  have h1hi : cdf μ1 q1 = 1 :=
    condLaw_cdf_one h.RM_meas hAm hPA0 (fun ω hω => (hAr ω hω).2.1.le)
  have h1lo : cdf μ1 q0 = 0 := condLaw_cdf_zero h.RM_meas hAm hPA0 (fun ω hω => (hAr ω hω).1)
  have h2hi : cdf μ2 q3 = 1 :=
    condLaw_cdf_one h.RM_meas hBm hPB0 (fun ω hω => (hBr ω hω).2.1.le)
  have h2lo : cdf μ2 q1 = 0 := condLaw_cdf_zero h.RM_meas hBm hPB0 (fun ω hω => (hBr ω hω).1)
  set T : Ω → ℝ := fun ω => qB μ2 q1 q3 (cdf μ1 (RM ω)) with hT
  set S : Ω → ℝ := fun ω => qB μ1 q0 q1 (cdf μ2 (RM ω)) with hS
  have hTm : Measurable T :=
    (qB_measurable μ2 hq13 h2hi).comp ((cdf μ1).mono.measurable.comp h.RM_meas)
  have hSm : Measurable S :=
    (qB_measurable μ1 hq01 h1hi).comp ((cdf μ2).mono.measurable.comp h.RM_meas)
  have hTlaw : (P[|A]).map T = (P[|B]).map RM := by
    have : (P[|A]).map T = ((P[|A]).map RM).map (fun y => qB μ2 q1 q3 (cdf μ1 y)) := by
      rw [Measure.map_map (show Measurable (fun y => qB μ2 q1 q3 (cdf μ1 y)) from
        (qB_measurable μ2 hq13 h2hi).comp (cdf μ1).mono.measurable) h.RM_meas]
      rfl
    rw [this, map_qB_cdf μ2 μ1 hc1 hc2 hq13 h2hi h2lo]
  have hSlaw : (P[|B]).map S = (P[|A]).map RM := by
    have : (P[|B]).map S = ((P[|B]).map RM).map (fun y => qB μ1 q0 q1 (cdf μ2 y)) := by
      rw [Measure.map_map (show Measurable (fun y => qB μ1 q0 q1 (cdf μ2 y)) from
        (qB_measurable μ1 hq01 h1hi).comp (cdf μ2).mono.measurable) h.RM_meas]
      rfl
    rw [this, map_qB_cdf μ1 μ2 hc2 hc1 hq01 h1hi h1lo]
  have hTr : ∀ ω, q1 ≤ T ω ∧ T ω ≤ q3 := fun ω => qB_mem μ2 hq13 h2hi _
  have hSr : ∀ ω, q0 ≤ S ω ∧ S ω ≤ q1 := fun ω => qB_mem μ1 hq01 h1hi _
  -- the swapped payoff
  set X : Ω → ℝ := fun ω => RM ω + A.indicator (fun ω => T ω - RM ω) ω +
    B.indicator (fun ω => S ω - RM ω) ω with hX
  have hXA : ∀ ω ∈ A, X ω = T ω := fun ω hω => by
    simp only [hX, indicator_of_mem hω, indicator_of_notMem (disjoint_left.1 hdisj hω)]; ring
  have hXB : ∀ ω ∈ B, X ω = S ω := fun ω hω => by
    simp only [hX, indicator_of_mem hω, indicator_of_notMem (disjoint_right.1 hdisj hω)]; ring
  have hXC : ∀ ω, ω ∉ A → ω ∉ B → X ω = RM ω := fun ω h1 h2 => by
    simp only [hX, indicator_of_notMem h1, indicator_of_notMem h2]; ring
  have hXm : Measurable X :=
    (h.RM_meas.add ((hTm.sub h.RM_meas).indicator hAm)).add ((hSm.sub h.RM_meas).indicator hBm)
  -- the law is unchanged
  have hlaw : P.map X = P.map RM := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply hXm hs, Measure.map_apply h.RM_meas hs]
    have key : ∀ E : Set Ω, MeasurableSet E →
        P E = P (E ∩ A) + P (E ∩ B) + P (E \ (A ∪ B)) := by
      intro E hE
      have s1 : (E \ A) ∩ B = E ∩ B := by
        ext ω; simp only [mem_inter_iff, mem_diff]
        constructor
        · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, disjoint_right.1 hdisj h2⟩, h2⟩
      have s2 : (E \ A) \ B = E \ (A ∪ B) := diff_diff
      rw [← measure_inter_add_diff E hAm, ← measure_inter_add_diff (E \ A) hBm, s1, s2,
        add_assoc]
    rw [key _ (hXm hs), key _ (h.RM_meas hs)]
    have e1 : X ⁻¹' s ∩ A = A ∩ T ⁻¹' s := by
      ext ω; simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩; rw [hXA ω h2] at h1; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; rw [← hXA ω h1] at h2; exact ⟨h2, h1⟩
    have e2 : X ⁻¹' s ∩ B = B ∩ S ⁻¹' s := by
      ext ω; simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩; rw [hXB ω h2] at h1; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; rw [← hXB ω h1] at h2; exact ⟨h2, h1⟩
    have e3 : X ⁻¹' s \ (A ∪ B) = RM ⁻¹' s \ (A ∪ B) := by
      ext ω; simp only [mem_diff, mem_preimage, mem_union, not_or]
      constructor
      · rintro ⟨h1, h2, h3⟩; rw [hXC ω h2 h3] at h1; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; rw [← hXC ω h2 h3] at h1; exact ⟨h1, h2, h3⟩
    rw [e1, e2, e3, inter_eq_of_condLaw_eq hAm hBm hmass hTm h.RM_meas hTlaw hs,
      inter_eq_of_condLaw_eq hBm hAm hmass.symm hSm h.RM_meas hSlaw hs,
      inter_comm (RM ⁻¹' s) A, inter_comm (RM ⁻¹' s) B, add_comm (P (B ∩ RM ⁻¹' s))]
  -- integrability and cost
  have hTA : ∀ ω ∈ A, |T ω - RM ω| ≤ q3 - q0 := fun ω hω => by
    rw [abs_le]; constructor <;> linarith [(hTr ω).1, (hTr ω).2, (hAr ω hω).1, (hAr ω hω).2.1]
  have hSB : ∀ ω ∈ B, |S ω - RM ω| ≤ q3 - q0 := fun ω hω => by
    rw [abs_le]; constructor <;> linarith [(hSr ω).1, (hSr ω).2, (hBr ω hω).1, (hBr ω hω).2.1]
  have hTRA : IntegrableOn (fun ω => T ω - RM ω) A P :=
    intOn_of_bdd hAm (hTm.sub h.RM_meas).aestronglyMeasurable hTA
  have hSRB : IntegrableOn (fun ω => S ω - RM ω) B P :=
    intOn_of_bdd hBm (hSm.sub h.RM_meas).aestronglyMeasurable hSB
  have hmtTA : IntegrableOn (fun ω => mt ω * (T ω - RM ω)) A P := by
    refine (h.mt_int.restrict (s := A)).mul_bdd (c := q3 - q0)
      (hTm.sub h.RM_meas).aestronglyMeasurable.restrict ?_ |>.congr
        (Eventually.of_forall fun ω => by simp [mul_comm])
    refine (ae_restrict_iff' hAm).2 (Eventually.of_forall fun ω hω => ?_)
    rw [Real.norm_eq_abs]; exact hTA ω hω
  have hmtSB : IntegrableOn (fun ω => mt ω * (S ω - RM ω)) B P := by
    refine (h.mt_int.restrict (s := B)).mul_bdd (c := q3 - q0)
      (hSm.sub h.RM_meas).aestronglyMeasurable.restrict ?_ |>.congr
        (Eventually.of_forall fun ω => by simp [mul_comm])
    refine (ae_restrict_iff' hBm).2 (Eventually.of_forall fun ω hω => ?_)
    rw [Real.norm_eq_abs]; exact hSB ω hω
  have hdecomp : (fun ω => mt ω * X ω) = fun ω => mt ω * RM ω +
      A.indicator (fun ω => mt ω * (T ω - RM ω)) ω +
      B.indicator (fun ω => mt ω * (S ω - RM ω)) ω := by
    funext ω
    by_cases ha : ω ∈ A
    · rw [hXA ω ha, indicator_of_mem ha, indicator_of_notMem (disjoint_left.1 hdisj ha)]; ring
    · by_cases hb : ω ∈ B
      · rw [hXB ω hb, indicator_of_mem hb, indicator_of_notMem ha]; ring
      · rw [hXC ω ha hb, indicator_of_notMem ha, indicator_of_notMem hb]; ring
  have hIA : Integrable (A.indicator (fun ω => mt ω * (T ω - RM ω))) P :=
    (integrable_indicator_iff hAm).2 hmtTA
  have hIB : Integrable (B.indicator (fun ω => mt ω * (S ω - RM ω))) P :=
    (integrable_indicator_iff hBm).2 hmtSB
  have hint : Integrable (fun ω => mt ω * X ω) P := by
    rw [hdecomp]; exact (h.budget_int.add hIA).add hIB
  have hcostEq : ∫ ω, mt ω * X ω ∂P = 1 + (∫ ω in A, mt ω * (T ω - RM ω) ∂P) +
      ∫ ω in B, mt ω * (S ω - RM ω) ∂P := by
    have i1 : ∫ ω, (mt ω * RM ω + A.indicator (fun ω => mt ω * (T ω - RM ω)) ω) +
        B.indicator (fun ω => mt ω * (S ω - RM ω)) ω ∂P =
        (∫ ω, mt ω * RM ω + A.indicator (fun ω => mt ω * (T ω - RM ω)) ω ∂P) +
          ∫ ω, B.indicator (fun ω => mt ω * (S ω - RM ω)) ω ∂P :=
      integral_add (h.budget_int.add hIA) hIB
    have i2 : ∫ ω, mt ω * RM ω + A.indicator (fun ω => mt ω * (T ω - RM ω)) ω ∂P =
        (∫ ω, mt ω * RM ω ∂P) + ∫ ω, A.indicator (fun ω => mt ω * (T ω - RM ω)) ω ∂P :=
      integral_add h.budget_int hIA
    rw [hdecomp, i1, i2, h.budget, integral_indicator hAm, integral_indicator hBm]
  -- the mean of the swapped values is preserved
  have hmeanA : ∫ ω in A, T ω ∂P = ∫ ω in B, RM ω ∂P := by
    rw [setIntegral_eq_condLaw hPA0 hTm, setIntegral_eq_condLaw hPB0 h.RM_meas, hTlaw, hmass]
  have hmeanB : ∫ ω in B, S ω ∂P = ∫ ω in A, RM ω ∂P := by
    rw [setIntegral_eq_condLaw hPB0 hSm, setIntegral_eq_condLaw hPA0 h.RM_meas, hSlaw, hmass]
  have hRA : IntegrableOn RM A P := intOn_of_bdd hAm h.RM_meas.aestronglyMeasurable
    (C := |q0| + |q1|) (fun ω hω => by
      rw [abs_le]; constructor <;>
        linarith [(hAr ω hω).1, (hAr ω hω).2.1, abs_nonneg q0, abs_nonneg q1, neg_abs_le q0,
          le_abs_self q1])
  have hRB : IntegrableOn RM B P := intOn_of_bdd hBm h.RM_meas.aestronglyMeasurable
    (C := |q1| + |q3|) (fun ω hω => by
      rw [abs_le]; constructor <;>
        linarith [(hBr ω hω).1, (hBr ω hω).2.1, abs_nonneg q1, abs_nonneg q3, neg_abs_le q1,
          le_abs_self q3])
  have hTA' : IntegrableOn T A P := by
    have := hTRA.add hRA
    exact this.congr_fun (fun ω _ => by simp) hAm
  have hSB' : IntegrableOn S B P := by
    have := hSRB.add hRB
    exact this.congr_fun (fun ω _ => by simp) hBm
  have hsum : (∫ ω in A, (T ω - RM ω) ∂P) + ∫ ω in B, (S ω - RM ω) ∂P = 0 := by
    rw [integral_sub hTA' hRA, integral_sub hSB' hRB, hmeanA, hmeanB]; ring
  -- strict saving on `A`
  have hposA : 0 < ∫ ω in A, (q2 - mt ω) * (T ω - RM ω) ∂P := by
    have hnn : 0 ≤ᵐ[P.restrict A] fun ω => (q2 - mt ω) * (T ω - RM ω) :=
      (ae_restrict_iff' hAm).2 (Eventually.of_forall fun ω hω => mul_nonneg
        (by linarith [(hAr ω hω).2.2]) (by linarith [(hTr ω).1, (hAr ω hω).2.1]))
    have hiA : IntegrableOn (fun ω => (q2 - mt ω) * (T ω - RM ω)) A P := by
      have : IntegrableOn (fun ω => q2 * (T ω - RM ω) - mt ω * (T ω - RM ω)) A P :=
        (hTRA.const_mul q2).sub hmtTA
      exact IntegrableOn.congr_fun this (fun ω _ => by ring) hAm
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hiA]
    have : Function.support (fun ω => (q2 - mt ω) * (T ω - RM ω)) ∩ A = A := by
      ext ω; simp only [mem_inter_iff, Function.mem_support]
      constructor
      · rintro ⟨-, h2⟩; exact h2
      · intro hω
        refine ⟨mul_ne_zero (by linarith [(hAr ω hω).2.2]) (by
          linarith [(hTr ω).1, (hAr ω hω).2.1]), hω⟩
    rw [this]; exact pos_iff_ne_zero.2 hPA0
  -- weak saving on `B`
  have hnegB : ∫ ω in B, (mt ω - q2) * (S ω - RM ω) ∂P ≤ 0 := by
    apply setIntegral_nonpos hBm
    intro ω hω
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith [(hBr ω hω).2.2])
      (by linarith [(hSr ω).2, (hBr ω hω).1])
  have eA : ∫ ω in A, (q2 - mt ω) * (T ω - RM ω) ∂P =
      q2 * (∫ ω in A, (T ω - RM ω) ∂P) - ∫ ω in A, mt ω * (T ω - RM ω) ∂P := by
    rw [← integral_const_mul, ← integral_sub (hTRA.const_mul q2) hmtTA]
    congr 1; funext ω; ring
  have eB : ∫ ω in B, (mt ω - q2) * (S ω - RM ω) ∂P =
      (∫ ω in B, mt ω * (S ω - RM ω) ∂P) - q2 * ∫ ω in B, (S ω - RM ω) ∂P := by
    rw [← integral_const_mul, ← integral_sub hmtSB (hSRB.const_mul q2)]
    congr 1; funext ω; ring
  have hcost : ∫ ω, mt ω * X ω ∂P < 1 := by
    rw [hcostEq]
    have : q2 * ((∫ ω in A, (T ω - RM ω) ∂P) + ∫ ω in B, (S ω - RM ω) ∂P) = 0 := by
      rw [hsum, mul_zero]
    nlinarith [eA, eB, hposA, hnegB]
  exact h.improve hXm hlaw hint hcost

end Ctx

end BCK


open MeasureTheory ProbabilityTheory Filter Topology Set BetaCoskew.ThreeMoment

namespace BCK

namespace Ctx

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {u w : ℝ → ℝ} {mt RM : Ω → ℝ}

/-- Unbounded form of anti-comonotonicity. -/
lemma anti' (h : Ctx P u w mt RM) (x q : ℝ) :
    P {ω | RM ω < x ∧ mt ω < q} = 0 ∨ P {ω | x < RM ω ∧ q < mt ω} = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hU1 : {ω | RM ω < x ∧ mt ω < q} =
      ⋃ n : ℕ, {ω | x - ((n : ℝ) + 1) < RM ω ∧ RM ω < x ∧ mt ω < q} := by
    ext ω; simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨ha, hb⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (x - RM ω)
      exact ⟨n, by linarith, ha, hb⟩
    · rintro ⟨n, -, ha, hb⟩; exact ⟨ha, hb⟩
  have hU2 : {ω | x < RM ω ∧ q < mt ω} =
      ⋃ n : ℕ, {ω | x < RM ω ∧ RM ω < x + ((n : ℝ) + 1) ∧ q < mt ω} := by
    ext ω; simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨ha, hb⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (RM ω - x)
      exact ⟨n, ha, by linarith, hb⟩
    · rintro ⟨n, ha, -, hb⟩; exact ⟨ha, hb⟩
  rw [hU1] at h1
  rw [hU2] at h2
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P {ω | x - ((n : ℝ) + 1) < RM ω ∧ RM ω < x ∧ mt ω < q} ≠ 0 := by
    by_contra hc; push Not at hc; exact h1 (measure_iUnion_null hc)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, P {ω | x < RM ω ∧ RM ω < x + ((k : ℝ) + 1) ∧ q < mt ω} ≠ 0 := by
    by_contra hc; push Not at hc; exact h2 (measure_iUnion_null hc)
  rcases h.anti (x - ((n : ℝ) + 1)) x q (x + ((k : ℝ) + 1)) with h3 | h3
  · exact hn h3
  · exact hk h3

/-- A cut of the market-return axis at kernel level `q`. -/
lemma cut (h : Ctx P u w mt RM) (q : ℝ) : ∃ D : Set ℝ, MeasurableSet D ∧
    (∀ᵐ ω ∂P, RM ω ∈ D → q ≤ mt ω) ∧ (∀ᵐ ω ∂P, RM ω ∉ D → mt ω ≤ q) := by
  set L : ℝ → ENNReal := fun x => P {ω | RM ω < x ∧ mt ω < q} with hL
  have hLmono : Monotone L := by
    intro x y hxy
    exact measure_mono fun ω hω => ⟨lt_of_lt_of_le hω.1 hxy, hω.2⟩
  set D : Set ℝ := {x | ∃ y, x < y ∧ L y = 0} with hD
  have hDopen : IsOpen D := by
    have : D = ⋃ y ∈ {y | L y = 0}, Iio y := by
      ext x; simp only [hD, mem_setOf_eq, mem_iUnion, mem_Iio, exists_prop]
      constructor
      · rintro ⟨y, h1, h2⟩; exact ⟨y, h2, h1⟩
      · rintro ⟨y, h1, h2⟩; exact ⟨y, h2, h1⟩
    rw [this]; exact isOpen_biUnion fun _ _ => isOpen_Iio
  refine ⟨D, hDopen.measurableSet, ?_, ?_⟩
  · -- below the cut, the kernel is at least `q`
    have hsub : {ω | RM ω ∈ D ∧ mt ω < q} ⊆
        ⋃ r : {r : ℚ // L r = 0}, {ω | RM ω < (r : ℝ) ∧ mt ω < q} := by
      rintro ω ⟨⟨y, hy1, hy2⟩, hmt⟩
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hy1
      have hLr : L r = 0 := le_antisymm (hy2 ▸ hLmono hr2.le) (zero_le')
      exact mem_iUnion.2 ⟨⟨r, hLr⟩, hr1, hmt⟩
    have hnull : P {ω | RM ω ∈ D ∧ mt ω < q} = 0 :=
      measure_mono_null hsub (measure_iUnion_null fun r => r.2)
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hnull
    simp only [mem_setOf_eq, _root_.not_imp, not_le] at hω
    exact hω
  · -- above the cut, the kernel is at most `q`
    set E : Set Ω := {ω | RM ω ∉ D ∧ ∀ r : ℚ, (r : ℝ) < RM ω → L r = 0} with hE
    have hEnull : P E = 0 := by
      rcases E.eq_empty_or_nonempty with he | ⟨ω0, hω0⟩
      · rw [he, measure_empty]
      · refine measure_mono_null (fun ω hω => ?_) (h.noAtoms' (RM ω0))
        simp only [mem_setOf_eq]
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
          exact hω.1 ⟨r, hr1, hω0.2 r hr2⟩
        · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hlt
          exact hω0.1 ⟨r, hr1, hω.2 r hr2⟩
    have hsub : {ω | RM ω ∉ D ∧ q < mt ω} ⊆
        (⋃ r : {r : ℚ // L r ≠ 0}, {ω | (r : ℝ) < RM ω ∧ q < mt ω}) ∪ E := by
      rintro ω ⟨hD', hmt⟩
      by_cases hall : ∀ r : ℚ, (r : ℝ) < RM ω → L r = 0
      · exact Or.inr ⟨hD', hall⟩
      · push Not at hall
        obtain ⟨r, hr1, hr2⟩ := hall
        exact Or.inl (mem_iUnion.2 ⟨⟨r, hr2⟩, hr1, hmt⟩)
    have hnull : P {ω | RM ω ∉ D ∧ q < mt ω} = 0 := by
      refine measure_mono_null hsub (measure_union_null (measure_iUnion_null fun r => ?_) hEnull)
      rcases h.anti' (r : ℝ) q with h1 | h1
      · exact absurd h1 r.2
      · exact h1
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hnull
    simp only [mem_setOf_eq, _root_.not_imp, not_le] at hω
    exact hω

end Ctx

end BCK


open MeasureTheory ProbabilityTheory Filter Topology Set BetaCoskew.ThreeMoment

namespace BCK

namespace Ctx

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {u w : ℝ → ℝ} {mt RM : Ω → ℝ}

lemma int_ind_mt (h : Ctx P u w mt RM) {S : Set ℝ} (hS : MeasurableSet S) :
    Integrable (fun ω => S.indicator (fun _ => (1:ℝ)) (RM ω) * mt ω) P := by
  refine h.mt_int.bdd_mul (c := 1) (((measurable_const.indicator hS).comp
    h.RM_meas)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  by_cases hx : RM ω ∈ S
  · simp [indicator_of_mem hx]
  · simp [indicator_of_notMem hx]

lemma int_ind_g (h : Ctx P u w mt RM) {S : Set ℝ} (hS : MeasurableSet S) {a : ℝ} (ha : 0 < a) :
    Integrable (fun ω => (S ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * gfun P u w RM ω) P := by
  have hb : ∀ᵐ ω ∂P, ‖S.indicator (fun _ => (1:ℝ)) (RM ω)‖ ≤ 1 :=
    Eventually.of_forall fun ω => by
      by_cases hx : RM ω ∈ S
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
  have h1 := (int_g_tail h ha).bdd_mul (c := 1) (((measurable_const.indicator hS).comp
    h.RM_meas)).aestronglyMeasurable hb
  refine h1.congr (Eventually.of_forall fun ω => ?_)
  by_cases h1 : RM ω ∈ S <;> by_cases h2 : RM ω ∈ Ioi a <;> simp [indicator, h1, h2]

/-- A set on which the kernel strictly exceeds `g / λ` (or falls strictly below) is null. -/
lemma null_of_strict (h : Ctx P u w mt RM) {lam : ℝ} (hlam : 0 < lam)
    (hrel : ∀ a, 0 < a →
      (∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * gfun P u w RM ω ∂P) =
        lam * ∫ ω, (Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) * mt ω ∂P)
    {B : Set ℝ} (hB : MeasurableSet B) {a : ℝ} (ha : 0 < a) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (hstrict : ∀ᵐ ω ∂P, RM ω ∈ B ∩ Ioi a → 0 < sgn * (lam * mt ω - gfun P u w RM ω)) :
    P {ω | RM ω ∈ B ∩ Ioi a} = 0 := by
  have hBa : MeasurableSet (B ∩ Ioi a) := hB.inter measurableSet_Ioi
  have hts := tail_set h hlam.le hrel ha hB
  set f : Ω → ℝ := fun ω => (B ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) *
    (sgn * (lam * mt ω - gfun P u w RM ω)) with hf
  have hfint : Integrable f P := by
    have := ((int_ind_mt h hBa).const_mul (sgn * lam)).sub ((int_ind_g h hB ha).const_mul sgn)
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [hf, Pi.sub_apply]; ring
  have hf0 : ∫ ω, f ω ∂P = 0 := by
    have e : (fun ω => f ω) = fun ω => (sgn * lam) * ((B ∩ Ioi a).indicator (fun _ => (1:ℝ))
        (RM ω) * mt ω) - sgn * ((B ∩ Ioi a).indicator (fun _ => (1:ℝ)) (RM ω) *
        gfun P u w RM ω) := by
      funext ω; simp only [hf]; ring
    rw [e, integral_sub ((int_ind_mt h hBa).const_mul _) ((int_ind_g h hB ha).const_mul _),
      integral_const_mul, integral_const_mul, hts]
    ring
  have hfnn : 0 ≤ᵐ[P] f := by
    filter_upwards [hstrict] with ω hω
    simp only [hf, Pi.zero_apply]
    by_cases hx : RM ω ∈ B ∩ Ioi a
    · rw [indicator_of_mem hx, one_mul]; exact (hω hx).le
    · rw [indicator_of_notMem hx, zero_mul]
  have hfz := (integral_eq_zero_iff_of_nonneg_ae hfnn hfint).1 hf0
  have hnull : ∀ᵐ ω ∂P, ¬ (RM ω ∈ B ∩ Ioi a) := by
    filter_upwards [hfz, hstrict] with ω h1 h2 hx
    simp only [hf, Pi.zero_apply, indicator_of_mem hx, one_mul] at h1
    have := h2 hx
    linarith
  rw [ae_iff] at hnull
  simpa using hnull

/-- The first-order kernel identity in the standing context. -/
theorem kernel (h : Ctx P u w mt RM) : ∃ lam : ℝ, 0 < lam ∧
    mt =ᵐ[P] fun ω => lam⁻¹ *
      (deriv w (1 - cdf (P.map RM) (RM ω)) * deriv u (RM ω)) := by
  obtain ⟨lam, hlam, hrel⟩ := tail_lam h
  refine ⟨lam, hlam, ?_⟩
  set kf : ℝ → ℝ := fun y => deriv u y * deriv w (1 - cdf (P.map RM) y) / lam with hkf
  have hkfm : Measurable kf :=
    (((measurable_deriv u).mul ((measurable_deriv w).comp (measurable_const.sub
      (cdf (P.map RM)).mono.measurable))).div_const lam)
  have hg : ∀ ω, gfun P u w RM ω = lam * kf (RM ω) := by
    intro ω; simp only [gfun, hkf]; field_simp
  choose D hDm hD1 hD2 using h.cut
  have hpos := h.pos
  -- `mt ≤ k(R_M)` a.s.
  have hup : P {ω | kf (RM ω) < mt ω} = 0 := by
    have hsub : {ω | kf (RM ω) < mt ω} ⊆
        (⋃ q : ℚ, ⋃ n : ℕ, {ω | RM ω ∈ (D q ∩ {y | kf y < q}) ∩ Ioi (1 / ((n : ℝ) + 1))}) ∪
        (⋃ q : ℚ, {ω | RM ω ∉ D q ∧ (q : ℝ) < mt ω}) ∪ {ω | RM ω ≤ 0} := by
      intro ω hω
      replace hω : kf (RM ω) < mt ω := hω
      by_cases hr : 0 < RM ω
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hω
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
        by_cases hD : RM ω ∈ D q
        · exact Or.inl (Or.inl (mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨n, ⟨hD, hq1⟩, hn⟩⟩))
        · exact Or.inl (Or.inr (mem_iUnion.2 ⟨q, hD, hq2⟩))
      · exact Or.inr (not_lt.1 hr)
    refine measure_mono_null hsub (measure_union_null (measure_union_null
      (measure_iUnion_null fun q => measure_iUnion_null fun n => ?_)
      (measure_iUnion_null fun q => ?_)) ?_)
    · refine null_of_strict h hlam hrel ((hDm q).inter (measurableSet_lt hkfm measurable_const))
        (by positivity) 1 (Or.inl rfl) ?_
      filter_upwards [hD1 q] with ω h1 hx
      have hq := h1 hx.1.1
      have hk : kf (RM ω) < q := hx.1.2
      rw [hg ω, one_mul, ← mul_sub]
      exact mul_pos hlam (by linarith)
    · have := hD2 q
      rw [ae_iff] at this
      refine measure_mono_null (fun ω hω => ?_) this
      simp only [mem_setOf_eq, _root_.not_imp, not_le] at hω ⊢
      exact hω
    · have := hpos; rw [ae_iff] at this; simpa [not_lt] using this
  -- `mt ≥ k(R_M)` a.s.
  have hdown : P {ω | mt ω < kf (RM ω)} = 0 := by
    have hsub : {ω | mt ω < kf (RM ω)} ⊆
        (⋃ q : ℚ, ⋃ n : ℕ, {ω | RM ω ∈ ((D q)ᶜ ∩ {y | (q : ℝ) < kf y}) ∩
          Ioi (1 / ((n : ℝ) + 1))}) ∪
        (⋃ q : ℚ, {ω | RM ω ∈ D q ∧ mt ω < (q : ℝ)}) ∪ {ω | RM ω ≤ 0} := by
      intro ω hω
      replace hω : mt ω < kf (RM ω) := hω
      by_cases hr : 0 < RM ω
      · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hω
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
        by_cases hD : RM ω ∈ D q
        · exact Or.inl (Or.inr (mem_iUnion.2 ⟨q, hD, hq1⟩))
        · exact Or.inl (Or.inl (mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨n, ⟨hD, hq2⟩, hn⟩⟩))
      · exact Or.inr (not_lt.1 hr)
    refine measure_mono_null hsub (measure_union_null (measure_union_null
      (measure_iUnion_null fun q => measure_iUnion_null fun n => ?_)
      (measure_iUnion_null fun q => ?_)) ?_)
    · refine null_of_strict h hlam hrel ((hDm q).compl.inter
        (measurableSet_lt measurable_const hkfm)) (by positivity) (-1) (Or.inr rfl) ?_
      filter_upwards [hD2 q] with ω h1 hx
      have hq := h1 hx.1.1
      have hk : (q : ℝ) < kf (RM ω) := hx.1.2
      rw [hg ω, ← mul_sub]
      nlinarith
    · have := hD1 q
      rw [ae_iff] at this
      refine measure_mono_null (fun ω hω => ?_) this
      simp only [mem_setOf_eq, _root_.not_imp, not_le] at hω ⊢
      exact hω
    · have := hpos; rw [ae_iff] at this; simpa [not_lt] using this
  have h1 : ∀ᵐ ω ∂P, ¬ kf (RM ω) < mt ω := by rw [ae_iff]; simpa using hup
  have h2 : ∀ᵐ ω ∂P, ¬ mt ω < kf (RM ω) := by rw [ae_iff]; simpa using hdown
  filter_upwards [h1, h2] with ω ha hb
  rw [le_antisymm (not_lt.1 ha) (not_lt.1 hb)]
  simp only [hkf]
  field_simp

end Ctx

end BCK


open MeasureTheory ProbabilityTheory Filter Topology Set BetaCoskew.ThreeMoment

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : Atomless P)
    (u w : ℝ → ℝ) (hu : UtilityAssumption u) (hw : WeightingAssumption w)
    (rf : ℝ) (mt : Ω → ℝ) {n : ℕ} (R : Fin n → Ω → ℝ)
    (hmkt : IsPricedMarket P mt rf R)
    (xM : Fin n → ℝ) (hxM : ∑ i, xM i = 1)
    (hEq : IsEquilibrium P u w mt (fun ω => ∑ i, xM i * R i ω))
    (hF : Continuous (cdf (P.map (fun ω => ∑ i, xM i * R i ω)))) :
    let RM : Ω → ℝ := fun ω => ∑ i, xM i * R i ω
    ∃ lam : ℝ, 0 < lam ∧
      mt =ᵐ[P] fun ω => lam⁻¹ *
        (deriv w (1 - cdf (P.map RM) (RM ω)) * deriv u (RM ω)) := by
  intro RM
  have hRM : Measurable RM :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (hmkt.measurable_R i)
  exact BCK.Ctx.kernel (P := P) (u := u) (w := w) (mt := mt) (RM := RM)
    ⟨hu, hw, hmkt.measurable_mt, hmkt.pos, hmkt.integrable_mt, hRM, hEq, hF⟩
