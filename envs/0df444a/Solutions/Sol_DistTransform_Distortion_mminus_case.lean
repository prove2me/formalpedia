-- Prove2me | solution 1 for DistTransform.Distortion.mminus_case
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:54:06.843096+00:00
-- url     : https://prove2.me/submissions/d817d37b-59bf-4fe9-aa15-27340906a5df

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model
import Theorems.Thm_DistTransform_Distortion_remark_p4

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

namespace Aux_DTDmm
open DistTransform.Distortion

lemma ioi_eq (μ : ProbabilityMeasure ℝ) (x : ℝ) :
    (μ : Measure ℝ) {ω | x < id ω} = ENNReal.ofReal (1 - cdf (μ : Measure ℝ) x) := by
  have h1 : {ω : ℝ | x < id ω} = (Set.Iic x)ᶜ := by ext; simp
  rw [h1, prob_compl_eq_one_sub measurableSet_Iic, cdf_eq_real, measureReal_def,
    ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one, ENNReal.ofReal_toReal
      (measure_ne_top _ _)]

lemma stLE_iff (F G : ProbabilityMeasure ℝ) :
    StLE F G ↔ ∀ x, cdf (G : Measure ℝ) x ≤ cdf (F : Measure ℝ) x := by
  unfold StLE StochasticOrders.Usual.UsualOrder
  refine forall_congr' fun x => ?_
  rw [ioi_eq, ioi_eq, ENNReal.ofReal_le_ofReal_iff]
  · constructor <;> intro h <;> linarith
  · linarith [cdf_le_one (G : Measure ℝ) x]

lemma qset_nonempty (F : ProbabilityMeasure ℝ) {p : ℝ} (hp1 : p < 1) :
    {x : ℝ | p ≤ cdf (F : Measure ℝ) x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop (μ := (F : Measure ℝ))).eventually
    (lt_mem_nhds hp1)).exists
  exact ⟨x, hx.le⟩

lemma qset_bdd (F : ProbabilityMeasure ℝ) {p : ℝ} (hp0 : 0 < p) :
    BddBelow {x : ℝ | p ≤ cdf (F : Measure ℝ) x} := by
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.1 ((tendsto_cdf_atBot (μ := (F : Measure ℝ))).eventually
    (gt_mem_nhds hp0))
  refine ⟨a, fun x hx => ?_⟩
  by_contra hxa
  push Not at hxa
  have := ha x hxa.le
  simp only [Set.mem_setOf_eq] at hx
  linarith

lemma leftQuantile_mono {F G : ProbabilityMeasure ℝ}
    (h : ∀ x, cdf (G : Measure ℝ) x ≤ cdf (F : Measure ℝ) x) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) : leftQuantile F p ≤ leftQuantile G p := by
  unfold leftQuantile
  exact csInf_le_csInf (qset_bdd F hp0) (qset_nonempty G hp1)
    (fun x hx => le_trans hx (h x))

/-- The left quantile at level `u ∈ (0,1)` is the least point of `{x : u ≤ F(x)}`. -/
lemma leftQuantile_isLeast (F : ProbabilityMeasure ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    IsLeast {x : ℝ | u ≤ cdf (F : Measure ℝ) x} (leftQuantile F u) := by
  have hne := qset_nonempty F hu1
  refine ⟨?_, fun x hx => csInf_le (qset_bdd F hu0) hx⟩
  show u ≤ cdf (F : Measure ℝ) (sInf {y : ℝ | u ≤ cdf (F : Measure ℝ) y})
  rw [← (cdf (F : Measure ℝ)).iInf_Ioi_eq]
  apply le_ciInf
  intro r
  obtain ⟨y, hyS, hyr⟩ := exists_lt_of_csInf_lt hne r.2
  exact hyS.trans (monotone_cdf _ hyr.le)

lemma cdf_map (F : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (hf : Measurable f) (x : ℝ) :
    cdf ((F.map hf.aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) x =
      (F : Measure ℝ).real (f ⁻¹' Set.Iic x) := by
  rw [cdf_eq_real, ProbabilityMeasure.toMeasure_map, measureReal_def, measureReal_def,
    Measure.map_apply hf measurableSet_Iic]

/-- A distribution with `F(a) = 0` and `F(b) = 1` lies in `M∞`. -/
lemma mem_Minf_of (G : ProbabilityMeasure ℝ) (a b : ℝ) (ha : cdf (G : Measure ℝ) a = 0)
    (hb : cdf (G : Measure ℝ) b = 1) : G ∈ Minf := by
  have hab : a ≤ b := by
    by_contra hlt
    push Not at hlt
    have := monotone_cdf (G : Measure ℝ) hlt.le
    linarith
  refine ⟨a, b, ?_⟩
  apply le_antisymm prob_le_one
  have hIoc : (G : Measure ℝ).real (Set.Ioc a b) = 1 := by
    have hset : Set.Ioc a b = Set.Iic b \ Set.Iic a := by
      ext z; simp only [Set.mem_Ioc, Set.mem_diff, Set.mem_Iic, not_le]; tauto
    rw [hset, measureReal_diff (Set.Iic_subset_Iic.2 hab) measurableSet_Iic]
    rw [cdf_eq_real] at ha hb
    rw [ha, hb]; norm_num
  have h1 : (G : Measure ℝ) (Set.Ioc a b) = 1 := by
    rw [measureReal_def] at hIoc
    have := (ENNReal.toReal_eq_one_iff _).1 hIoc
    exact this
  calc (1 : ENNReal) = (G : Measure ℝ) (Set.Ioc a b) := h1.symm
    _ ≤ (G : Measure ℝ) (Set.Icc a b) := measure_mono Set.Ioc_subset_Icc_self


lemma galois (F : ProbabilityMeasure ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) (x : ℝ) :
    leftQuantile F u ≤ x ↔ u ≤ cdf (F : Measure ℝ) x := by
  constructor
  · intro hq
    exact (leftQuantile_isLeast F hu0 hu1).1.trans (monotone_cdf _ hq)
  · intro hx
    exact (leftQuantile_isLeast F hu0 hu1).2 hx

lemma leftQuantile_level_mono (F : ProbabilityMeasure ℝ) {p p' : ℝ} (hp0 : 0 < p)
    (hpp : p ≤ p') (hp'1 : p' < 1) : leftQuantile F p ≤ leftQuantile F p' := by
  unfold leftQuantile
  exact csInf_le_csInf (qset_bdd F hp0) (qset_nonempty F hp'1)
    (fun x hx => le_trans hpp hx)

lemma unif_le (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | p ≤ c} = c := by
  rw [measureReal_def, Measure.restrict_apply' measurableSet_Ioo]
  have h1 : volume ({p : ℝ | p ≤ c} ∩ Set.Ioo 0 1) = ENNReal.ofReal c := by
    apply le_antisymm
    · calc volume ({p : ℝ | p ≤ c} ∩ Set.Ioo 0 1) ≤ volume (Set.Ioc (0:ℝ) c) := by
            apply measure_mono
            rintro p ⟨hp, hp0, _⟩
            exact ⟨hp0, hp⟩
        _ = ENNReal.ofReal c := by rw [Real.volume_Ioc]; simp
    · calc ENNReal.ofReal c = volume (Set.Ioo (0:ℝ) c) := by rw [Real.volume_Ioo]; simp
        _ ≤ volume ({p : ℝ | p ≤ c} ∩ Set.Ioo 0 1) := by
            apply measure_mono
            rintro p ⟨hp0, hp⟩
            exact ⟨le_of_lt hp, hp0, lt_of_lt_of_le hp hc1⟩
  rw [h1, ENNReal.toReal_ofReal hc0]

lemma cdf_eq_unif_quantile (G : ProbabilityMeasure ℝ) (x : ℝ) :
    cdf (G : Measure ℝ) x =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).real {p | leftQuantile G p ≤ x} := by
  have hr := (remark_p4 id (monotoneOn_id) (fun p hp => ⟨hp.1, hp.2.le⟩)).2.2
    (fun p hp => hp.2) G x
  simp only [id] at hr
  rw [hr, unif_le _ (cdf_nonneg _ _) (cdf_le_one _ _)]

lemma restrict_mono_Ioo (S S' : Set ℝ) (h : ∀ p ∈ Set.Ioo (0:ℝ) 1, p ∈ S → p ∈ S') :
    (volume.restrict (Set.Ioo (0 : ℝ) 1)).real S ≤
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).real S' := by
  rw [measureReal_def, measureReal_def, Measure.restrict_apply' measurableSet_Ioo,
    Measure.restrict_apply' measurableSet_Ioo]
  apply ENNReal.toReal_mono
  · exact ne_top_of_le_ne_top (b := volume (Set.Ioo (0:ℝ) 1))
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top) (measure_mono Set.inter_subset_right)
  · apply measure_mono
    rintro p ⟨hp, hp'⟩
    exact ⟨h p hp' hp, hp'⟩

instance unif_prob : IsProbabilityMeasure (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; simp⟩

/-- `law(f_n(X)) → law(f(X))` weakly when `f_n → f` pointwise (dominated convergence). -/
lemma tendsto_map_of_pointwise (F : ProbabilityMeasure ℝ) (fs : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hfs : ∀ n, Measurable (fs n)) (hf : Measurable f)
    (hlim : ∀ y, Tendsto (fun n => fs n y) atTop (𝓝 (f y))) (hfc : ∀ n, Continuous (fs n))
    (hfc' : Continuous f) :
    Tendsto (fun n => F.map (hfs n).aemeasurable) atTop (𝓝 (F.map hf.aemeasurable)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro g
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [integral_map hf.aemeasurable g.continuous.aestronglyMeasurable]
  simp_rw [integral_map (hfs _).aemeasurable g.continuous.aestronglyMeasurable]
  refine tendsto_integral_of_dominated_convergence (fun _ => ‖g‖) (fun n => ?_)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun y => g.norm_coe_le_norm _)
    (Filter.Eventually.of_forall fun y => ?_)
  · exact (g.continuous.comp (hfc n)).aestronglyMeasurable
  · exact (g.continuous.tendsto _).comp (hlim y)


lemma meas_max (c : ℝ) : Measurable (fun y : ℝ => max y c) := measurable_id.max measurable_const

lemma cdf_max_lt (F : ProbabilityMeasure ℝ) (c y : ℝ) (hy : y < c) :
    cdf ((F.map (meas_max c).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) y = 0 := by
  rw [cdf_map _ _ (meas_max c)]
  have : (fun z : ℝ => max z c) ⁻¹' Set.Iic y = ∅ := by
    ext z; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le hy (le_max_right z c)
  rw [this, measureReal_empty]

lemma cdf_max_ge (F : ProbabilityMeasure ℝ) (c y : ℝ) (hy : c ≤ y) :
    cdf ((F.map (meas_max c).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) y =
      cdf (F : Measure ℝ) y := by
  rw [cdf_map _ _ (meas_max c), cdf_eq_real]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_Iic, max_le_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hy⟩⟩

lemma cdf_max_le (F : ProbabilityMeasure ℝ) (c y : ℝ) :
    cdf ((F.map (meas_max c).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) y ≤
      cdf (F : Measure ℝ) y := by
  rw [cdf_map _ _ (meas_max c), cdf_eq_real]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro z hz
  simp only [Set.mem_preimage, Set.mem_Iic] at hz ⊢
  exact (le_max_left z c).trans hz

/-- Least-element description of the left quantile at a level `u ∈ (0,1]` with a nonempty
upper set. -/
lemma lq_isLeast' (F : ProbabilityMeasure ℝ) {u : ℝ} (hu0 : 0 < u)
    (hne : {x : ℝ | u ≤ cdf (F : Measure ℝ) x}.Nonempty) :
    IsLeast {x : ℝ | u ≤ cdf (F : Measure ℝ) x} (leftQuantile F u) := by
  refine ⟨?_, fun x hx => csInf_le (qset_bdd F hu0) hx⟩
  show u ≤ cdf (F : Measure ℝ) (sInf {y : ℝ | u ≤ cdf (F : Measure ℝ) y})
  rw [← (cdf (F : Measure ℝ)).iInf_Ioi_eq]
  apply le_ciInf
  intro r
  obtain ⟨y, hyS, hyr⟩ := exists_lt_of_csInf_lt hne r.2
  exact hyS.trans (monotone_cdf _ hyr.le)

/-- If `c < F⁻¹(u)`, the truncation `X ∨ c` has the same `u`-quantile. -/
lemma lq_max (F : ProbabilityMeasure ℝ) {u : ℝ} (hu0 : 0 < u)
    (hne : {x : ℝ | u ≤ cdf (F : Measure ℝ) x}.Nonempty) (c : ℝ) (hc : c < leftQuantile F u) :
    leftQuantile (F.map (meas_max c).aemeasurable) u = leftQuantile F u := by
  have hl := lq_isLeast' F hu0 hne
  apply IsLeast.csInf_eq
  refine ⟨?_, fun y hy => ?_⟩
  · show u ≤ cdf _ (leftQuantile F u)
    rw [cdf_max_ge F c _ hc.le]; exact hl.1
  · have hy' : u ≤ cdf ((F.map (meas_max c).aemeasurable : ProbabilityMeasure ℝ) : Measure ℝ) y :=
      hy
    rcases lt_or_ge y c with hyc | hyc
    · rw [cdf_max_lt F c y hyc] at hy'; linarith
    · rw [cdf_max_ge F c y hyc] at hy'; exact hl.2 hy'

lemma max_mem_Minf (F : ProbabilityMeasure ℝ) (b c : ℝ) (hb : cdf (F : Measure ℝ) b = 1) :
    (F.map (meas_max c).aemeasurable : ProbabilityMeasure ℝ) ∈ Minf := by
  apply mem_Minf_of _ (c - 1) (max b c)
  · exact cdf_max_lt F c _ (by linarith)
  · rw [cdf_max_ge F c _ (le_max_right _ _)]
    apply le_antisymm (cdf_le_one _ _)
    rw [← hb]; exact monotone_cdf _ (le_max_left _ _)

/-- The compressing map `φₙ(x) = x₀ + (x - x₀)/(n+1)` for `x < x₀`, `φₙ(x) = x` for `x ≥ x₀`. -/
noncomputable def phiFun (x0 : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  if x < x0 then x0 + (x - x0) / ((n : ℝ) + 1) else x

lemma phiFun_strictMono (x0 : ℝ) (n : ℕ) : StrictMono (phiFun x0 n) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  intro x y hxy
  unfold phiFun
  split_ifs with hx hy hy
  · have : (x - x0) / ((n : ℝ) + 1) < (y - x0) / ((n : ℝ) + 1) :=
      div_lt_div_of_pos_right (by linarith) hn
    linarith
  · have : (x - x0) / ((n : ℝ) + 1) < 0 := div_neg_of_neg_of_pos (by linarith) hn
    push Not at hy; linarith
  · linarith
  · exact hxy

lemma phiFun_surj (x0 : ℝ) (n : ℕ) : Function.Surjective (phiFun x0 n) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  intro y
  by_cases hy : y < x0
  · refine ⟨x0 + (y - x0) * ((n : ℝ) + 1), ?_⟩
    have hlt : x0 + (y - x0) * ((n : ℝ) + 1) < x0 := by nlinarith
    unfold phiFun
    rw [if_pos hlt]
    field_simp
    ring
  · exact ⟨y, by unfold phiFun; rw [if_neg hy]⟩

noncomputable def phi (x0 : ℝ) (n : ℕ) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (phiFun x0 n) (phiFun_strictMono x0 n) (phiFun_surj x0 n)

lemma phi_apply (x0 : ℝ) (n : ℕ) (x : ℝ) : phi x0 n x = phiFun x0 n x := rfl

lemma phiFun_le_max (x0 : ℝ) (n : ℕ) (x : ℝ) : phiFun x0 n x ≤ max x x0 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold phiFun
  split_ifs with hx
  · have : (x - x0) / ((n : ℝ) + 1) < 0 := div_neg_of_neg_of_pos (by linarith) hn
    linarith [le_max_right x x0]
  · exact le_max_left _ _

lemma phiFun_tendsto (x0 x : ℝ) :
    Tendsto (fun n : ℕ => phiFun x0 n x) atTop (𝓝 (max x x0)) := by
  by_cases hx : x < x0
  · simp only [phiFun, if_pos hx, max_eq_right hx.le]
    have h1 : Tendsto (fun n : ℕ => (x - x0) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa using (tendsto_const_nhds (x := x0)).add h1
  · push Not at hx
    simp only [phiFun, if_neg (not_lt.2 hx), max_eq_left hx]
    exact tendsto_const_nhds

end Aux_DTDmm

open DistTransform.Distortion Aux_DTDmm in
theorem solution (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ)
    (hlsc : IsLSC Set.univ T) (hmono : IsMonotoneT Set.univ T)
    (hcomm : CommutesWithShape Set.univ T)
    (h : ℝ → ℝ) (hh_mono : MonotoneOn h (Set.Ioo 0 1))
    (hh_range : ∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < h p ∧ h p ≤ 1)
    (h4 : ∀ F ∈ Minf, ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p = leftQuantile F (h p)) :
    ∀ F ∈ Mminus, ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p = leftQuantile F (h p) := by
  have qmono : ∀ F G : ProbabilityMeasure ℝ, (∀ x, cdf (G : Measure ℝ) x ≤ cdf (F : Measure ℝ) x) →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T F) p ≤ leftQuantile (T G) p := by
    intro F G hFG p hp
    exact leftQuantile_mono ((stLE_iff _ _).1 (hmono F trivial G trivial
      ((stLE_iff _ _).2 hFG))) hp.1 hp.2
  intro F hF p hp
  obtain ⟨⟨b, hb⟩, _⟩ := hF
  have hu0 : 0 < h p := (hh_range p hp).1
  have hne : {x : ℝ | h p ≤ cdf (F : Measure ℝ) x}.Nonempty :=
    ⟨b, by simp only [Set.mem_setOf_eq, hb]; exact (hh_range p hp).2⟩
  set x0 := leftQuantile F (h p) with hx0
  -- eq. (5): `q_p^T(F) ≤ F⁻¹(h(p))`, comparing with the truncation `X ∨ c`, `c < F⁻¹(h(p))`.
  have h5 : leftQuantile (T F) p ≤ x0 := by
    have e := h4 _ (max_mem_Minf F b (x0 - 1) hb) p hp
    rw [lq_max F hu0 hne (x0 - 1) (by linarith)] at e
    have := qmono F _ (cdf_max_le F (x0 - 1)) p hp
    rw [e] at this
    exact this
  apply le_antisymm h5
  -- reverse inequality via shape transforms `φₙ` and lower-semicontinuity
  set qF := leftQuantile (T F) p with hqF
  set c := qF - 1 with hc
  have hlim := tendsto_map_of_pointwise F (fun n => phi c n) (fun y => max y c)
    (fun n => (phi c n).continuous.measurable) (meas_max c)
    (fun y => by simpa only [phi_apply] using phiFun_tendsto c y)
    (fun n => (phi c n).continuous) (continuous_id.max continuous_const)
  set G := (T F).map (meas_max c).aemeasurable with hG
  have hle : ∀ n : ℕ, StLE (T (shape (phi c n) F)) G := by
    intro n
    rw [(hcomm (phi c n)).2 F trivial, stLE_iff]
    intro x
    rw [hG, cdf_map _ _ (meas_max c), shape, cdf_map _ _ (phi c n).continuous.measurable]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro y hy
    simp only [Set.mem_preimage, Set.mem_Iic] at hy ⊢
    rw [phi_apply]
    exact (phiFun_le_max c n y).trans hy
  have hTF0 := (stLE_iff _ _).1 (hlsc (fun n => shape (phi c n) F)
    (F.map (meas_max c).aemeasurable) G (fun _ => trivial) trivial trivial hlim hle)
  have h1 : leftQuantile (T (F.map (meas_max c).aemeasurable)) p ≤ leftQuantile G p :=
    leftQuantile_mono hTF0 hp.1 hp.2
  have h2 : leftQuantile G p ≤ qF := by
    rw [galois G hp.1 hp.2 qF, hG, cdf_max_ge (T F) c qF (by linarith)]
    exact (leftQuantile_isLeast (T F) hp.1 hp.2).1
  have e := h4 _ (max_mem_Minf F b c hb) p hp
  rw [lq_max F hu0 hne c (by linarith)] at e
  linarith
