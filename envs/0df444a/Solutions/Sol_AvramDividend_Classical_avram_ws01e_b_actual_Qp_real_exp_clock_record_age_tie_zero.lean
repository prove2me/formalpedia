-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_Qp_real_exp_clock_record_age_tie_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:48:28.875761+00:00
-- url     : https://prove2.me/submissions/c2f6ae08-6fd5-4a58-82b6-619b93081e7c

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
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

end S221TE

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b θ p : ℝ) (hb : 0 ≤ b) (hθ : 0 ≤ θ) (hp : 0 < p) :
    (let age : Ω → ℝ≥0 := fun ω => (twoSidedExitUpTime X b ω).toNNReal
     let Qp : Measure (Ω × ℝ) :=
       (P.prod (ProbabilityTheory.expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     Qp {z : Ω × ℝ | z.2 = (age z.1 : ℝ)} = 0) := by
  intro age Qp
  have hage : Measurable fun ω => ((age ω : ℝ≥0) : ℝ) :=
    measurable_coe_nnreal_real.comp (ENNReal.measurable_toNNReal.comp (S221TE.meas_T X b))
  have hS : MeasurableSet {z : Ω × ℝ | z.2 = (age z.1 : ℝ)} :=
    measurableSet_eq_fun measurable_snd (hage.comp measurable_fst)
  have := isProbabilityMeasure_expMeasure hp
  apply withDensity_absolutelyContinuous
  rw [Measure.prod_apply hS]
  have h0 : ∀ ω, expMeasure p (Prod.mk ω ⁻¹' {z : Ω × ℝ | z.2 = (age z.1 : ℝ)}) = 0 := by
    intro ω
    have : Prod.mk ω ⁻¹' {z : Ω × ℝ | z.2 = (age z.1 : ℝ)} = {((age ω : ℝ≥0) : ℝ)} := by
      ext r; simp
    rw [this]
    unfold expMeasure gammaMeasure
    exact withDensity_absolutelyContinuous _ _ Real.volume_singleton
  exact (lintegral_congr fun ω => h0 ω).trans lintegral_zero
