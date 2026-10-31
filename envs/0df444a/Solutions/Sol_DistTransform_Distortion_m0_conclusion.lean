-- Prove2me | solution 1 for DistTransform.Distortion.m0_conclusion
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T21:44:24.984795+00:00
-- url     : https://prove2.me/submissions/97f94789-a913-40cd-8c65-140476a1e99a

import Mathlib
import Definitions.Def_DistTransform_Distortion_Model
import Theorems.Thm_DistTransform_Distortion_eq_4
import Theorems.Thm_DistTransform_Distortion_mminus_case
import Theorems.Thm_DistTransform_Distortion_mplus_case

open MeasureTheory ProbabilityTheory Filter Topology

namespace Aux_DTDm0
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

end Aux_DTDm0

open DistTransform.Distortion Aux_DTDm0 in
theorem solution (T : ProbabilityMeasure ℝ → ProbabilityMeasure ℝ)
    (hlsc : IsLSC Set.univ T) (hmono : IsMonotoneT Set.univ T)
    (hcomm : CommutesWithShape Set.univ T) :
    ∃ h : ℝ → ℝ, MonotoneOn h (Set.Ioo 0 1) ∧
      (∀ p ∈ Set.Ioo (0 : ℝ) 1, 0 < h p ∧ h p < 1) ∧
      ∀ (F : ProbabilityMeasure ℝ), ∀ p ∈ Set.Ioo (0 : ℝ) 1,
        leftQuantile (T F) p = leftQuantile F (h p) := by
  obtain ⟨h, hh_mono, hh_range, h4⟩ :=
    eq_4 Set.univ (Or.inl rfl) T (Set.mapsTo_univ _ _) hlsc hmono hcomm
  have hminus := mminus_case T hlsc hmono hcomm h hh_mono hh_range h4
  obtain ⟨hlt1, hplus⟩ := mplus_case T hlsc hmono hcomm h hh_mono hh_range h4
  refine ⟨h, hh_mono, fun p hp => ⟨(hh_range p hp).1, hlt1 p hp⟩, ?_⟩
  -- the identity holds on distributions bounded above and on those bounded below
  have hbddAbove : ∀ G : ProbabilityMeasure ℝ, (∃ b, cdf (G : Measure ℝ) b = 1) →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T G) p = leftQuantile G (h p) := by
    intro G ⟨b, hb⟩ p hp
    by_cases hpos : ∀ a, 0 < cdf (G : Measure ℝ) a
    · exact hminus G ⟨⟨b, hb⟩, hpos⟩ p hp
    · push Not at hpos
      obtain ⟨a, ha⟩ := hpos
      exact h4 G (mem_Minf_of G a b (le_antisymm ha (cdf_nonneg _ _)) hb) p hp
  have hbddBelow : ∀ G : ProbabilityMeasure ℝ, (∃ a, cdf (G : Measure ℝ) a = 0) →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, leftQuantile (T G) p = leftQuantile G (h p) := by
    intro G ⟨a, ha⟩ p hp
    by_cases hlt : ∀ b, cdf (G : Measure ℝ) b < 1
    · exact hplus G ⟨⟨a, ha⟩, hlt⟩ p hp
    · push Not at hlt
      obtain ⟨b, hb⟩ := hlt
      exact h4 G (mem_Minf_of G a b ha (le_antisymm (cdf_le_one _ _) hb)) p hp
  -- sandwich a general distribution between truncations
  intro F p hp
  have hq0 : 0 < h p := (hh_range p hp).1
  have hq1 : h p < 1 := hlt1 p hp
  set q := h p with hq
  set x0 := leftQuantile F q with hx0
  have hleast := leftQuantile_isLeast F hq0 hq1
  rw [← hx0] at hleast
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℝ, x0 < n ∧ -n < x0 :=
    ⟨|x0| + 1, by linarith [le_abs_self x0], by linarith [neg_abs_le x0]⟩
  have hmin : Measurable (fun y : ℝ => min y n) := measurable_id.min measurable_const
  have hmax : Measurable (fun y : ℝ => max y (-n)) := measurable_id.max measurable_const
  set Fn := F.map hmin.aemeasurable with hFn
  set Gn := F.map hmax.aemeasurable with hGn
  have cFn_lt : ∀ y, y < n → cdf (Fn : Measure ℝ) y = cdf (F : Measure ℝ) y := by
    intro y hy
    rw [hFn, cdf_map _ _ hmin, cdf_eq_real]
    congr 1
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic, min_le_iff]
    constructor
    · rintro (h | h)
      · exact h
      · linarith
    · intro h; exact Or.inl h
  have cFn_ge : ∀ y, n ≤ y → cdf (Fn : Measure ℝ) y = 1 := by
    intro y hy
    rw [hFn, cdf_map _ _ hmin]
    have : (fun z : ℝ => min z n) ⁻¹' Set.Iic y = Set.univ := by
      ext z; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
      exact (min_le_right z n).trans hy
    rw [this, probReal_univ]
  have cFn_ge_F : ∀ y, cdf (F : Measure ℝ) y ≤ cdf (Fn : Measure ℝ) y := by
    intro y
    rw [hFn, cdf_map _ _ hmin, cdf_eq_real]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro z hz
    simp only [Set.mem_preimage, Set.mem_Iic] at hz ⊢
    exact (min_le_left z n).trans hz
  have cGn_lt : ∀ y, y < -n → cdf (Gn : Measure ℝ) y = 0 := by
    intro y hy
    rw [hGn, cdf_map _ _ hmax]
    have : (fun z : ℝ => max z (-n)) ⁻¹' Set.Iic y = ∅ := by
      ext z; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false,
        not_le]
      exact lt_of_lt_of_le hy (le_max_right z (-n))
    rw [this, measureReal_empty]
  have cGn_ge : ∀ y, -n ≤ y → cdf (Gn : Measure ℝ) y = cdf (F : Measure ℝ) y := by
    intro y hy
    rw [hGn, cdf_map _ _ hmax, cdf_eq_real]
    congr 1
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic, max_le_iff]
    constructor
    · rintro ⟨h, _⟩; exact h
    · intro h; exact ⟨h, hy⟩
  have cGn_le_F : ∀ y, cdf (Gn : Measure ℝ) y ≤ cdf (F : Measure ℝ) y := by
    intro y
    rw [hGn, cdf_map _ _ hmax, cdf_eq_real]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro z hz
    simp only [Set.mem_preimage, Set.mem_Iic] at hz ⊢
    exact (le_max_left z (-n)).trans hz
  -- quantiles of the truncations at level `q` coincide with that of `F`
  have hqFn : leftQuantile Fn q = x0 := by
    apply IsLeast.csInf_eq
    refine ⟨le_trans hleast.1 (cFn_ge_F x0), fun y hy => ?_⟩
    rcases lt_or_ge y n with hyn | hyn
    · have hy' : q ≤ cdf (F : Measure ℝ) y := by
        have : q ≤ cdf (Fn : Measure ℝ) y := hy
        rwa [cFn_lt y hyn] at this
      exact hleast.2 hy'
    · linarith
  have hqGn : leftQuantile Gn q = x0 := by
    apply IsLeast.csInf_eq
    refine ⟨?_, fun y hy => ?_⟩
    · show q ≤ cdf (Gn : Measure ℝ) x0
      rw [cGn_ge x0 hn2.le]; exact hleast.1
    · have hy' : q ≤ cdf (Gn : Measure ℝ) y := hy
      rcases lt_or_ge y (-n) with hyn | hyn
      · rw [cGn_lt y hyn] at hy'; linarith
      · rw [cGn_ge y hyn] at hy'; exact hleast.2 hy'
  have hFn_eq := hbddAbove Fn ⟨n, cFn_ge n le_rfl⟩ p hp
  have hGn_eq := hbddBelow Gn ⟨-n - 1, cGn_lt _ (by linarith)⟩ p hp
  rw [← hq, hqFn] at hFn_eq
  rw [← hq, hqGn] at hGn_eq
  -- monotonicity: `Fn ⩽st F ⩽st Gn`
  have hle1 : leftQuantile (T Fn) p ≤ leftQuantile (T F) p :=
    leftQuantile_mono ((stLE_iff _ _).1 (hmono Fn trivial F trivial
      ((stLE_iff _ _).2 cFn_ge_F))) hp.1 hp.2
  have hle2 : leftQuantile (T F) p ≤ leftQuantile (T Gn) p :=
    leftQuantile_mono ((stLE_iff _ _).1 (hmono F trivial Gn trivial
      ((stLE_iff _ _).2 cGn_le_F))) hp.1 hp.2
  linarith
