-- Prove2me | solution 1 for FBMSP.theorem3_model_market_comparison
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:30:56.60542+00:00
-- url     : https://prove2.me/submissions/b890cfb5-3c8a-4ea9-b103-a87da8e0fec4

import Definitions.Def_FBMSP_Model
import Theorems.Thm_FBMSP_singlePrice_attains
import Theorems.Thm_FBMSP_lemma1_pricing_geometry

open MeasureTheory Set Filter FBMSP
open scoped BigOperators

private lemma mm_menu_nonneg (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) :
    0 ≤ menuAt η x P := by
  classical
  unfold menuAt
  split_ifs <;> simp_all only [le_max_iff, le_refl, true_or]

private lemma mm_menu_le (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) (b : ℝ)
    (hb : 0 ≤ b) (h : ∀ p ∈ P, postedRevenue η x p ≤ b) : menuAt η x P ≤ b := by
  classical
  unfold menuAt
  split_ifs with hP
  · exact max_le hb (Finset.sup'_le _ _ h)
  · exact hb

private lemma mm_le_menu (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) (p : ℝ)
    (hp : p ∈ P) : postedRevenue η x p ≤ menuAt η x P := by
  classical
  have hP : P.Nonempty := ⟨p, hp⟩
  rw [menuAt, dif_pos hP]
  exact (Finset.le_sup' (fun q => postedRevenue η x q) hp).trans (le_max_right _ _)

private lemma mm_menu_mono (η : Measure ℝ) (x : ℝ) : Monotone (menuAt η x) := by
  intro A B hAB
  exact mm_menu_le η x A _ (mm_menu_nonneg η x B) (fun p hp => mm_le_menu η x B p (hAB hp))

private lemma mm_menu_insert (η : Measure ℝ) (x p : ℝ) (P : Finset ℝ) :
    menuAt η x (insert p P) = max (menuAt η x P) (postedRevenue η x p) := by
  classical
  apply le_antisymm
  · apply mm_menu_le η x _ _ ((mm_menu_nonneg η x P).trans (le_max_left _ _))
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact le_max_right _ _
    · exact (mm_le_menu η x P q hq).trans (le_max_left _ _)
  · exact max_le (mm_menu_mono η x (Finset.subset_insert p P))
      (mm_le_menu η x _ p (Finset.mem_insert_self p P))

private lemma mm_menu_union (η : Measure ℝ) (x : ℝ) (A B : Finset ℝ) :
    menuAt η x (A ∪ B) = max (menuAt η x A) (menuAt η x B) := by
  classical
  apply le_antisymm
  · apply mm_menu_le η x _ _ ((mm_menu_nonneg η x A).trans (le_max_left _ _))
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (mm_le_menu η x A p hp).trans (le_max_left _ _)
    · exact (mm_le_menu η x B p hp).trans (le_max_right _ _)
  · exact max_le (mm_menu_mono η x Finset.subset_union_left)
      (mm_menu_mono η x Finset.subset_union_right)

private lemma mm_posted_integrable (ν η : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] (p : ℝ) :
    Integrable (fun x => postedRevenue η x p) ν := by
  have hs : Antitone (survival η) := by
    intro a b hab
    exact ENNReal.toReal_mono (measure_ne_top η (Ici a))
      (measure_mono (Ici_subset_Ici.mpr hab))
  have hm : Measurable (fun x => postedRevenue η x p) :=
    measurable_const.mul (hs.measurable.comp (measurable_const.sub measurable_id))
  apply (integrable_const (|p| : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with x
  have hS : survival η (p - x) ≤ 1 := measureReal_le_one
  have hS0 : 0 ≤ survival η (p - x) := ENNReal.toReal_nonneg
  simp only [postedRevenue, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hS0]
  simpa using mul_le_mul_of_nonneg_left hS (abs_nonneg p)

private lemma mm_menu_integrable (ν η : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] (P : Finset ℝ) :
    Integrable (fun x => menuAt η x P) ν := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa [menuAt] using (integrable_const (0 : ℝ) : Integrable (fun _ : ℝ => 0) ν)
  | @insert p P hp ih =>
    simpa only [mm_menu_insert, Pi.sup_def] using
      ih.sup (mm_posted_integrable ν η p)

private lemma mm_survival_le_one (η : Measure ℝ) [IsProbabilityMeasure η] (t : ℝ) :
    survival η t ≤ 1 := by
  simpa only [survival, Measure.real] using (measureReal_le_one (μ := η) (s := Ici t))

private lemma mm_posted_mono (η : Measure ℝ) [IsProbabilityMeasure η] (p : ℝ)
    (hp : 0 ≤ p) : Monotone (fun x => postedRevenue η x p) := by
  intro x y hxy
  apply mul_le_mul_of_nonneg_left ?_ hp
  exact ENNReal.toReal_mono (measure_ne_top η (Ici (p - y)))
    (measure_mono (Ici_subset_Ici.mpr (sub_le_sub_left hxy p)))

private lemma mm_single_nonneg (η : Measure ℝ) (hη : ValidNoise η)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ singleRevenue η x := by
  obtain ⟨ha, hr⟩ := singlePrice_attains η hη x hx
  rw [← hr]
  exact mul_nonneg ha.1.1 ENNReal.toReal_nonneg

private lemma mm_single_mono (η : Measure ℝ) (hη : ValidNoise η) :
    Monotone (fun x : ℝ => singleRevenue η (max x 0)) := by
  letI : IsProbabilityMeasure η := hη.1
  intro x y hxy
  change singleRevenue η (max x 0) ≤ singleRevenue η (max y 0)
  obtain ⟨ha, hr⟩ := singlePrice_attains η hη (max x 0) (le_max_right x 0)
  obtain ⟨hb, hs⟩ := singlePrice_attains η hη (max y 0) (le_max_right y 0)
  rw [← hr, ← hs]
  exact (mm_posted_mono η (singlePrice η (max x 0)) ha.1.1
    (max_le_max hxy le_rfl)).trans (hb.1.2 _ ha.1.1)

private lemma mm_posted_le_mean (η : Measure ℝ) (hη : ValidNoise η) (x p : ℝ)
    (hV : ∀ᵐ e ∂η, 0 ≤ x + e) : postedRevenue η x p ≤ x := by
  letI : IsProbabilityMeasure η := hη.1
  have hv : Integrable (fun e : ℝ => e + x) η := hη.2.1.add (integrable_const x)
  have hp : Integrable (fun _ : ℝ => p) η := integrable_const p
  have htail := setIntegral_mono_on hp.integrableOn hv.integrableOn measurableSet_Ici
    (fun e (he : e ∈ Ici (p - x)) => by change p - x ≤ e at he; linarith)
  have hbound : postedRevenue η x p ≤ ∫ e in Ici (p - x), e + x ∂η := by
    simpa only [setIntegral_const, smul_eq_mul, postedRevenue, survival, Measure.real, mul_comm]
      using htail
  have hnonneg : 0 ≤ᵐ[η] (fun e : ℝ => e + x) := by
    change ∀ᵐ e ∂η, 0 ≤ e + x
    simpa only [add_comm] using hV
  calc
    postedRevenue η x p ≤ ∫ e in Ici (p - x), e + x ∂η := hbound
    _ ≤ ∫ e, e + x ∂η := setIntegral_le_integral hv hnonneg
    _ = x := by rw [integral_add hη.2.1 (integrable_const x), hη.2.2]; simp

private lemma mm_single_le_mean (η : Measure ℝ) (hη : ValidNoise η)
    (x : ℝ) (hx : 0 ≤ x) (hV : ∀ᵐ e ∂η, 0 ≤ x + e) : singleRevenue η x ≤ x := by
  rw [← (singlePrice_attains η hη x hx).2]
  exact mm_posted_le_mean η hη x _ hV

private lemma mm_single_integrable (ν η : Measure ℝ) (hν : ValidPredictions ν)
    (hη : ValidNoise η) (hV : NonnegativeValuations ν η) :
    Integrable (singleRevenue η) ν := by
  have hmeas : AEStronglyMeasurable (singleRevenue η) ν := by
    apply (mm_single_mono η hη).measurable.aestronglyMeasurable.congr
    filter_upwards [hν.2.2] with x hx
    simp only [max_eq_left hx]
  apply hν.2.1.mono' hmeas
  filter_upwards [hν.2.2, hV] with x hx hVx
  rw [Real.norm_eq_abs, abs_of_nonneg (mm_single_nonneg η hη x hx)]
  exact mm_single_le_mean η hη x hx hVx

private lemma mm_menuRevenue_le_mean (ν η : Measure ℝ) (hν : ValidPredictions ν)
    (hη : ValidNoise η) (hV : NonnegativeValuations ν η) (P : Finset ℝ) :
    menuRevenue ν η P ≤ predictionMean ν := by
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure η := hη.1
  apply integral_mono_ae (mm_menu_integrable ν η P) hν.2.1
  filter_upwards [hν.2.2, hV] with x hx hVx
  exact mm_menu_le η x P x hx (fun p hp => mm_posted_le_mean η hη x p hVx)

private lemma mm_bddAbove (ν η : Measure ℝ) (hν : ValidPredictions ν)
    (hη : ValidNoise η) (hV : NonnegativeValuations ν η) (k : ℕ) :
    BddAbove {r : ℝ | ∃ P : Finset ℝ, FeasibleMenu P k ∧ r = menuRevenue ν η P} := by
  refine ⟨predictionMean ν, ?_⟩
  rintro r ⟨P, hP, rfl⟩
  exact mm_menuRevenue_le_mean ν η hν hη hV P

private lemma mm_single_difference (η : Measure ℝ) (hη : ValidNoise η)
    (x p : ℝ) (hp : 0 < p) (hpx : p ≤ x) :
    singleRevenue η x - singleRevenue η p ≤ x - p := by
  letI : IsProbabilityMeasure η := hη.1
  rcases eq_or_lt_of_le hpx with rfl | hpx
  · simp
  have h := (lemma1_pricing_geometry η hη).2.1 p x hp hpx
  exact h.2.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (mm_survival_le_one η (margin η x)) (sub_nonneg.mpr hpx.le))

private lemma mm_posted_dirac (x p : ℝ) :
    postedRevenue (Measure.dirac 0) x p = if p ≤ x then p else 0 := by
  by_cases hpx : p ≤ x
  · simp [postedRevenue, survival, Measure.dirac_apply', hpx, sub_nonpos.mpr hpx]
  · have hh : ¬ p - x ≤ 0 := by linarith
    simp [postedRevenue, survival, Measure.dirac_apply', hpx, hh]

private lemma mm_lift_pointwise (η : Measure ℝ) (hη : ValidNoise η)
    (P : Finset ℝ) (hP : ∀ p ∈ P, 0 ≤ p) (x : ℝ) (hx : 0 ≤ x)
    (hV : ∀ᵐ e ∂η, 0 ≤ x + e) :
    singleRevenue η x + menuAt (Measure.dirac 0) x P ≤
      x + menuAt η x (P.image (singlePrice η)) := by
  classical
  letI : IsProbabilityMeasure η := hη.1
  let Q := P.image (singlePrice η)
  have hbase : 0 ≤ x - singleRevenue η x + menuAt η x Q := by
    linarith [mm_single_le_mean η hη x hx hV, mm_menu_nonneg η x Q]
  have hmenu : menuAt (Measure.dirac 0) x P ≤
      x - singleRevenue η x + menuAt η x Q := by
    apply mm_menu_le _ _ _ _ hbase
    intro p hp
    rw [mm_posted_dirac]
    by_cases hpx : p ≤ x
    · rw [if_pos hpx]
      by_cases hp0 : p = 0
      · simpa only [hp0] using hbase
      have hpos : 0 < p := lt_of_le_of_ne (hP p hp) (Ne.symm hp0)
      have hatt := singlePrice_attains η hη p hpos.le
      have hQ : singlePrice η p ∈ Q := Finset.mem_image.mpr ⟨p, hp, rfl⟩
      have hrev : singleRevenue η p ≤ menuAt η x Q := by
        rw [← hatt.2]
        exact (mm_posted_mono η _ hatt.1.1.1 hpx).trans (mm_le_menu η x Q _ hQ)
      linarith [mm_single_difference η hη x p hpos hpx]
    · rw [if_neg hpx]
      exact hbase
  dsimp [Q] at hmenu
  linarith

theorem solution (ν η : MeasureTheory.Measure ℝ)
    (hν : ValidPredictions ν) (hη : ValidNoise η)
    (hV : NonnegativeValuations ν η) (k : ℕ) (hk : 1 ≤ k) :
    segmentationLoss ν η k ≤ predictionMean ν - modelRevenue ν k := by
  classical
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure η := hη.1
  have hsingle := mm_single_integrable ν η hν hη hV
  have hbound := mm_bddAbove ν η hν hη hV k
  have hmodel : modelRevenue ν k ≤
      predictionMean ν - personalizedRevenue ν η + optimalRevenue ν η k := by
    refine csSup_le ?_ ?_
    · refine ⟨0, ∅, ⟨by simp, by simp⟩, ?_⟩
      simp [menuRevenue, menuAt]
    · rintro r ⟨P, hP, rfl⟩
      let Q := P.image (singlePrice η)
      have hQ : FeasibleMenu Q k := by
        refine ⟨(Finset.card_image_le).trans hP.1, ?_⟩
        intro q hq
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
        exact (singlePrice_attains η hη p (hP.2 p hp)).1.1.1
      have hpoint : ∀ᵐ x ∂ν,
          singleRevenue η x + menuAt (Measure.dirac 0) x P ≤ x + menuAt η x Q := by
        filter_upwards [hν.2.2, hV] with x hx hVx
        exact mm_lift_pointwise η hη P hP.2 x hx hVx
      have hint := integral_mono_ae
        (hsingle.add (mm_menu_integrable ν (Measure.dirac 0) P))
        (hν.2.1.add (mm_menu_integrable ν η Q)) hpoint
      simp only [Pi.add_apply] at hint
      rw [integral_add hsingle (mm_menu_integrable ν (Measure.dirac 0) P),
        integral_add hν.2.1 (mm_menu_integrable ν η Q)] at hint
      have hsup : menuRevenue ν η Q ≤ optimalRevenue ν η k :=
        le_csSup hbound ⟨Q, hQ, rfl⟩
      change personalizedRevenue ν η + menuRevenue ν (Measure.dirac 0) P ≤
        predictionMean ν + menuRevenue ν η Q at hint
      linarith
  unfold segmentationLoss
  linarith

