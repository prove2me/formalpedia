-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bi_new_record_upper_ray_ae_true_Qp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:02:33.565925+00:00
-- url     : https://prove2.me/submissions/85c5d6fc-43e7-44b5-b07f-7d39c6ff5b07

import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace S221TE


lemma meas_T {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) : Measurable (twoSidedExitUpTime X b) := by
  have hX : ∀ t, Measurable (X.X t) := fun t => (X.adapted t).mono (𝓕.le t) le_rfl
  have key : twoSidedExitUpTime X b = fun ω =>
      ⨅ q : ℚ, if b < X.X (Real.toNNReal q) ω then ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) else ⊤ := by
    funext ω
    apply le_antisymm
    · refine le_iInf fun q => ?_
      split_ifs with h
      · exact iInf₂_le (Real.toNNReal q) h
      · exact le_top
    · refine le_iInf₂ fun t ht => ?_
      refine le_of_forall_gt fun c hc => ?_
      have hev : ∀ᶠ s in nhdsWithin t (Ici t), b < X.X s ω :=
        (X.rightCont ω t).eventually (lt_mem_nhds ht)
      obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hev
      -- choose u' with t < u' ≤ u and u' < c
      obtain ⟨u', htu', hu'u, hu'c⟩ : ∃ u' : ℝ≥0, t < u' ∧ u' ≤ u ∧ (u' : ℝ≥0∞) < c := by
        obtain ⟨d, htd, hdc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
        refine ⟨min u d, lt_min hu (by exact_mod_cast htd), min_le_left _ _, ?_⟩
        exact lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hdc
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) < u' from htu')
      have hq0 : (0 : ℝ) ≤ q := le_trans t.2 hq1.le
      have hqt : Real.toNNReal q ∈ Ico t u := by
        constructor
        · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hq1.le
        · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
          exact lt_of_lt_of_le hq2 (by exact_mod_cast hu'u)
      have hb := hsub hqt
      refine lt_of_le_of_lt (iInf_le _ q) ?_
      rw [if_pos (show b < X.X _ ω from hb)]
      refine lt_of_le_of_lt ?_ hu'c
      have : Real.toNNReal q ≤ u' := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hq2.le
      exact_mod_cast this
  rw [key]
  refine Measurable.iInf fun q => ?_
  exact Measurable.ite (measurableSet_lt measurable_const (hX _)) measurable_const measurable_const



lemma meas_D {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) : Measurable (twoSidedExitDownTime X b) := by
  have hX : ∀ t, Measurable (X.X t) := fun t => (X.adapted t).mono (𝓕.le t) le_rfl
  have key : twoSidedExitDownTime X b = fun ω =>
      ⨅ q : ℚ, if X.X (Real.toNNReal q) ω < b then ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) else ⊤ := by
    funext ω
    apply le_antisymm
    · refine le_iInf fun q => ?_
      split_ifs with h
      · exact iInf₂_le (Real.toNNReal q) h
      · exact le_top
    · refine le_iInf₂ fun t ht => ?_
      refine le_of_forall_gt fun c hc => ?_
      have hev : ∀ᶠ s in nhdsWithin t (Ici t), X.X s ω < b :=
        (X.rightCont ω t).eventually (gt_mem_nhds ht)
      obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hev
      -- choose u' with t < u' ≤ u and u' < c
      obtain ⟨u', htu', hu'u, hu'c⟩ : ∃ u' : ℝ≥0, t < u' ∧ u' ≤ u ∧ (u' : ℝ≥0∞) < c := by
        obtain ⟨d, htd, hdc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hc
        refine ⟨min u d, lt_min hu (by exact_mod_cast htd), min_le_left _ _, ?_⟩
        exact lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hdc
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) < u' from htu')
      have hq0 : (0 : ℝ) ≤ q := le_trans t.2 hq1.le
      have hqt : Real.toNNReal q ∈ Ico t u := by
        constructor
        · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hq1.le
        · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
          exact lt_of_lt_of_le hq2 (by exact_mod_cast hu'u)
      have hb := hsub hqt
      refine lt_of_le_of_lt (iInf_le _ q) ?_
      rw [if_pos (show X.X _ ω < b from hb)]
      refine lt_of_le_of_lt ?_ hu'c
      have : Real.toNNReal q ≤ u' := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]; exact hq2.le
      exact_mod_cast this
  rw [key]
  refine Measurable.iInf fun q => ?_
  exact Measurable.ite (measurableSet_lt (hX _) measurable_const) measurable_const measurable_const


lemma iff_off {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (hb : 0 ≤ b) (z : Ω × ℝ) :
    (b < runningSup X (Real.toNNReal z.2) z.1 →
      twoSidedExitUpTime X b z.1 < ⊤ ∧ ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2) ∧
    (twoSidedExitUpTime X b z.1 < ⊤ → ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2 →
      z.2 ≠ ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) → b < runningSup X (Real.toNNReal z.2) z.1) := by
  set T := twoSidedExitUpTime X b with hT
  have key := avram_ws01e_b_runningSup_gt_iff_strict_upcrossing_before_horizon X b hb z.1 (Real.toNNReal z.2)
  change _ ↔ T z.1 < _ at key
  constructor
  · intro h0
    have h := key.1 h0
    have hfin : T z.1 < ⊤ := lt_of_lt_of_le h le_top
    refine ⟨hfin, ?_⟩
    have h1 : (T z.1).toNNReal < Real.toNNReal z.2 := by
      rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hfin.ne]; exact h
    have h2 : (0:ℝ) < z.2 := by
      by_contra hn; push Not at hn
      rw [Real.toNNReal_of_nonpos hn] at h1; exact absurd h1 (not_lt_zero)
    have := NNReal.coe_lt_coe.2 h1
    rw [Real.coe_toNNReal _ h2.le] at this; exact this.le
  · intro hfin hle hz'
    apply key.2
    have hlt : ((T z.1).toNNReal : ℝ) < z.2 := lt_of_le_of_ne hle (Ne.symm hz')
    have h1 : (T z.1).toNNReal < Real.toNNReal z.2 := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (le_trans (NNReal.coe_nonneg _) hle)]; exact hlt
    rw [← ENNReal.coe_toNNReal hfin.ne]; exact_mod_cast h1

lemma null {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b p : ℝ) (hp : 0 < p) (w : Ω × ℝ → ℝ≥0∞) :
    (P.prod (expMeasure p)).withDensity w
      {z : Ω × ℝ | z.2 = ((twoSidedExitUpTime X b z.1).toNNReal : ℝ)} = 0 := by
  set T := twoSidedExitUpTime X b with hT
  have hage : Measurable fun ω => (((T ω).toNNReal : ℝ≥0) : ℝ) :=
    measurable_coe_nnreal_real.comp (ENNReal.measurable_toNNReal.comp (meas_T X b))
  have hS : MeasurableSet {z : Ω × ℝ | z.2 = ((T z.1).toNNReal : ℝ)} :=
    measurableSet_eq_fun measurable_snd (hage.comp measurable_fst)
  have := isProbabilityMeasure_expMeasure hp
  apply withDensity_absolutelyContinuous
  rw [Measure.prod_apply hS]
  have h0 : ∀ ω, expMeasure p (Prod.mk ω ⁻¹' {z : Ω × ℝ | z.2 = ((T z.1).toNNReal : ℝ)}) = 0 := by
    intro ω
    have : Prod.mk ω ⁻¹' {z : Ω × ℝ | z.2 = ((T z.1).toNNReal : ℝ)} = {(((T ω).toNNReal : ℝ≥0) : ℝ)} := by
      ext r; simp
    rw [this]
    unfold expMeasure gammaMeasure
    exact withDensity_absolutelyContinuous _ _ Real.volume_singleton
  exact (lintegral_congr fun ω => h0 ω).trans lintegral_zero

lemma ae_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (hb : 0 ≤ b) (p : ℝ) (hp : 0 < p)
    (w : Ω × ℝ → ℝ≥0∞) :
    ({z : Ω × ℝ | b < runningSup X (Real.toNNReal z.2) z.1} : Set (Ω × ℝ)) =ᵐ[
      (P.prod (expMeasure p)).withDensity w]
      {z : Ω × ℝ | (twoSidedExitUpTime X b) z.1 < ⊤ ∧
        (((twoSidedExitUpTime X b) z.1).toNNReal : ℝ) ≤ z.2} := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (null X b p hp w)] with z hz
  have hz' : ¬ z.2 = ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) := hz
  apply propext
  show b < runningSup X (Real.toNNReal z.2) z.1 ↔ (twoSidedExitUpTime X b z.1 < ⊤ ∧ _)
  exact ⟨(iff_off X b hb z).1, fun h => (iff_off X b hb z).2 h.1 h.2 hz'⟩

end S221TE

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (b : ℝ) (hb : 0 ≤ b) :
    (let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal
        (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
     let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
     ({z : Ω × ℝ | b < runningSup X (Real.toNNReal z.2) z.1}) =ᵐ[Qp]
       {z : Ω × ℝ | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}) := by
  intro Qp T age
  exact S221TE.ae_eq X b hb p hp _
