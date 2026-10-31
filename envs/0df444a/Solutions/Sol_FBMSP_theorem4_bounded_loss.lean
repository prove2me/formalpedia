-- Prove2me | solution 1 for FBMSP.theorem4_bounded_loss
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:36:01.369018+00:00
-- url     : https://prove2.me/submissions/610ee261-d7b1-4d9d-bfe6-6b0676381e9f

import Theorems.Thm_FBMSP_singlePrice_attains

open MeasureTheory Set Filter FBMSP
open scoped BigOperators

namespace FBMSP

private lemma rb_menu_nonneg (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) :
    0 ≤ menuAt η x P := by
  classical
  unfold menuAt
  split_ifs <;> simp_all only [le_max_iff, le_refl, true_or]

private lemma rb_menu_le (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) (b : ℝ)
    (hb : 0 ≤ b) (h : ∀ p ∈ P, postedRevenue η x p ≤ b) : menuAt η x P ≤ b := by
  classical
  unfold menuAt
  split_ifs with hP
  · exact max_le hb (Finset.sup'_le _ _ h)
  · exact hb

private lemma rb_le_menu (η : Measure ℝ) (x : ℝ) (P : Finset ℝ) (p : ℝ)
    (hp : p ∈ P) : postedRevenue η x p ≤ menuAt η x P := by
  classical
  have hP : P.Nonempty := ⟨p, hp⟩
  rw [menuAt, dif_pos hP]
  exact (Finset.le_sup' (fun q => postedRevenue η x q) hp).trans (le_max_right _ _)

private lemma rb_menu_mono (η : Measure ℝ) (x : ℝ) : Monotone (menuAt η x) := by
  intro A B hAB
  exact rb_menu_le η x A _ (rb_menu_nonneg η x B) (fun p hp => rb_le_menu η x B p (hAB hp))

private lemma rb_menu_insert (η : Measure ℝ) (x p : ℝ) (P : Finset ℝ) :
    menuAt η x (insert p P) = max (menuAt η x P) (postedRevenue η x p) := by
  classical
  apply le_antisymm
  · apply rb_menu_le η x _ _ ((rb_menu_nonneg η x P).trans (le_max_left _ _))
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact le_max_right _ _
    · exact (rb_le_menu η x P q hq).trans (le_max_left _ _)
  · exact max_le (rb_menu_mono η x (Finset.subset_insert p P))
      (rb_le_menu η x _ p (Finset.mem_insert_self p P))

private lemma rb_posted_integrable (ν η : Measure ℝ)
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

private lemma rb_menu_integrable (ν η : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure η] (P : Finset ℝ) :
    Integrable (fun x => menuAt η x P) ν := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa [menuAt] using (integrable_const (0 : ℝ) : Integrable (fun _ : ℝ => 0) ν)
  | @insert p P hp ih =>
    have h := ih.sup (rb_posted_integrable ν η p)
    change Integrable (fun x => max (menuAt η x P) (postedRevenue η x p)) ν at h
    simpa only [rb_menu_insert] using h

private lemma rb_survival_le_one (η : Measure ℝ) [IsProbabilityMeasure η] (t : ℝ) :
    survival η t ≤ 1 := by
  simpa only [survival, Measure.real] using (measureReal_le_one (μ := η) (s := Ici t))

private lemma rb_posted_mono (η : Measure ℝ) [IsProbabilityMeasure η] (p : ℝ)
    (hp : 0 ≤ p) : Monotone (fun x => postedRevenue η x p) := by
  intro x y hxy
  apply mul_le_mul_of_nonneg_left ?_ hp
  exact ENNReal.toReal_mono (measure_ne_top η (Ici (p - y)))
    (measure_mono (Ici_subset_Ici.mpr (sub_le_sub_left hxy p)))

private lemma rb_single_nonneg (η : Measure ℝ) (hη : ValidNoise η)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ singleRevenue η x := by
  obtain ⟨ha, hr⟩ := singlePrice_attains η hη x hx
  rw [← hr]
  exact mul_nonneg ha.1.1 ENNReal.toReal_nonneg

private lemma rb_single_mono (η : Measure ℝ) (hη : ValidNoise η) :
    Monotone (fun x : ℝ => singleRevenue η (max x 0)) := by
  letI : IsProbabilityMeasure η := hη.1
  intro x y hxy
  change singleRevenue η (max x 0) ≤ singleRevenue η (max y 0)
  obtain ⟨ha, hr⟩ := singlePrice_attains η hη (max x 0) (le_max_right x 0)
  obtain ⟨hb, hs⟩ := singlePrice_attains η hη (max y 0) (le_max_right y 0)
  rw [← hr, ← hs]
  exact (rb_posted_mono η (singlePrice η (max x 0)) ha.1.1
    (max_le_max hxy le_rfl)).trans (hb.1.2 _ ha.1.1)

private lemma rb_margin_value (η : Measure ℝ) (hη : ValidNoise η)
    (x : ℝ) (hx : 0 ≤ x) :
    singleRevenue η x = (x + margin η x) * survival η (margin η x) := by
  rw [← (singlePrice_attains η hη x hx).2]
  unfold postedRevenue margin
  ring

private lemma rb_affine_le (η : Measure ℝ) (hη : ValidNoise η)
    (x θ : ℝ) (hx : 0 ≤ x) :
    (x + θ) * survival η θ ≤ singleRevenue η x := by
  by_cases hprice : 0 ≤ x + θ
  · have h := (singlePrice_attains η hη x hx).1.1.2 (x + θ) hprice
    rw [(singlePrice_attains η hη x hx).2] at h
    simpa only [postedRevenue, add_sub_cancel_left] using h
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hprice)
      ENNReal.toReal_nonneg).trans (rb_single_nonneg η hη x hx)

private lemma rb_single_difference (η : Measure ℝ) (hη : ValidNoise η)
    (x y : ℝ) (hy : 0 ≤ y) (hxy : y ≤ x) :
    singleRevenue η x - singleRevenue η y ≤ x - y := by
  letI : IsProbabilityMeasure η := hη.1
  have hx : 0 ≤ x := hy.trans hxy
  have hval := rb_margin_value η hη x hx
  have hlow := rb_affine_le η hη y (margin η x) hy
  have hS := mul_le_mul_of_nonneg_right (rb_survival_le_one η (margin η x))
    (sub_nonneg.mpr hxy)
  nlinarith only [hval, hlow, hS]

private lemma rb_single_le_base (η : Measure ℝ) (hη : ValidNoise η)
    (x : ℝ) (hx : 0 ≤ x) : singleRevenue η x ≤ x + singleRevenue η 0 := by
  have h := rb_single_difference η hη x 0 le_rfl hx
  linarith

private lemma rb_single_integrable (ν η : Measure ℝ) (hν : ValidPredictions ν)
    (hη : ValidNoise η) : Integrable (singleRevenue η) ν := by
  letI : IsProbabilityMeasure ν := hν.1
  have hmeas : AEStronglyMeasurable (singleRevenue η) ν := by
    apply (rb_single_mono η hη).measurable.aestronglyMeasurable.congr
    filter_upwards [hν.2.2] with x hx
    simp only [max_eq_left hx]
  apply (hν.2.1.add (integrable_const (singleRevenue η 0))).mono' hmeas
  filter_upwards [hν.2.2] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (rb_single_nonneg η hη x hx)]
  exact rb_single_le_base η hη x hx

private lemma rb_posted_le_single (η : Measure ℝ) (hη : ValidNoise η)
    (x p : ℝ) (hx : 0 ≤ x) : postedRevenue η x p ≤ singleRevenue η x := by
  have h := rb_affine_le η hη x (p - x) hx
  have heq : x + (p - x) = p := by ring
  simpa only [heq, postedRevenue] using h

private lemma rb_menu_le_single (η : Measure ℝ) (hη : ValidNoise η)
    (x : ℝ) (hx : 0 ≤ x) (P : Finset ℝ) : menuAt η x P ≤ singleRevenue η x := by
  exact rb_menu_le η x P _ (rb_single_nonneg η hη x hx)
    (fun p _ => rb_posted_le_single η hη x p hx)

private lemma rb_menuRevenue_le_personalized (ν η : Measure ℝ) (hν : ValidPredictions ν)
    (hη : ValidNoise η) (P : Finset ℝ) :
    menuRevenue ν η P ≤ personalizedRevenue ν η := by
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure η := hη.1
  apply integral_mono_ae (rb_menu_integrable ν η P) (rb_single_integrable ν η hν hη)
  filter_upwards [hν.2.2] with x hx
  exact rb_menu_le_single η hη x hx P

private lemma rb_revenue_bddAbove (ν η : Measure ℝ) (hν : ValidPredictions ν)
    (hη : ValidNoise η) (k : ℕ) :
    BddAbove {r : ℝ | ∃ P : Finset ℝ, FeasibleMenu P k ∧ r = menuRevenue ν η P} := by
  refine ⟨personalizedRevenue ν η, ?_⟩
  rintro r ⟨P, _, rfl⟩
  exact rb_menuRevenue_le_personalized ν η hν hη P

private lemma rb_menuRevenue_le_optimal (ν η : Measure ℝ) (hν : ValidPredictions ν)
    (hη : ValidNoise η) {P : Finset ℝ} {k : ℕ} (hP : FeasibleMenu P k) :
    menuRevenue ν η P ≤ optimalRevenue ν η k := by
  exact le_csSup (rb_revenue_bddAbove ν η hν hη k) ⟨P, hP, rfl⟩


private lemma uniform_grid_cover {k : ℕ} (hk : 1 ≤ k) (L U x : ℝ)
    (hx : x ∈ Icc L U) :
    ∃ j : Fin k,
      L + (j.val : ℝ) * ((U - L) / (k : ℝ)) ≤ x ∧
      x ≤ L + ((j.val : ℝ) + 1) * ((U - L) / (k : ℝ)) := by
  classical
  cases k with
  | zero => omega
  | succ k =>
      let δ : ℝ := (U - L) / ((k + 1 : ℕ) : ℝ)
      have hkne : (k : ℝ) + 1 ≠ 0 := by positivity
      have hspan : ((k : ℝ) + 1) * δ = U - L := by
        dsimp [δ]
        push_cast
        field_simp [hkne]
      let S : Finset (Fin (k + 1)) :=
        Finset.univ.filter (fun j => L + (j.val : ℝ) * δ ≤ x)
      have hS : S.Nonempty := by
        refine ⟨0, ?_⟩
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.val_zero, Nat.cast_zero, zero_mul, add_zero]
        exact hx.1
      let j : Fin (k + 1) := S.max' hS
      have hjlower : L + (j.val : ℝ) * δ ≤ x :=
        (Finset.mem_filter.mp (Finset.max'_mem S hS)).2
      refine ⟨j, hjlower, ?_⟩
      change x ≤ L + ((j.val : ℝ) + 1) * δ
      by_cases hjlast : j = Fin.last k
      · rw [hjlast]
        simp only [Fin.val_last]
        linarith [hx.2]
      · have hjne : j.val ≠ k := by
          intro heq
          exact hjlast (Fin.ext heq)
        have hjlt : j.val + 1 < k + 1 := by have := j.isLt; omega
        let l : Fin (k + 1) := ⟨j.val + 1, hjlt⟩
        by_contra hbad
        have hlmem : l ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
            l, Nat.cast_add, Nat.cast_one]
          exact le_of_lt (lt_of_not_ge hbad)
        have hmax : l ≤ j := Finset.le_max' S l hlmem
        change j.val + 1 ≤ j.val at hmax
        omega

end FBMSP

private lemma grid_menu_approximation (η : Measure ℝ) (hη : ValidNoise η)
    (L U : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ∃ P : Finset ℝ, FeasibleMenu P k ∧
      ∀ x : ℝ, 0 ≤ x → x ∈ Icc L U →
        singleRevenue η x - menuAt η x P ≤ (U - L) / (k : ℝ) := by
  classical
  letI : IsProbabilityMeasure η := hη.1
  let δ : ℝ := (U - L) / (k : ℝ)
  let anchor : Fin k → ℝ := fun j => max (L + (j.val : ℝ) * δ) 0
  let price : Fin k → ℝ := fun j => singlePrice η (anchor j)
  let P : Finset ℝ := Finset.univ.image price
  have hanchor (j : Fin k) : 0 ≤ anchor j := le_max_right _ _
  refine ⟨P, ⟨?_, ?_⟩, ?_⟩
  · exact (Finset.card_image_le).trans (by simp)
  · intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact (singlePrice_attains η hη (anchor j) (hanchor j)).1.1.1
  · intro x hx hRange
    obtain ⟨j, hjlo, hjhi⟩ := uniform_grid_cover hk L U x hRange
    have hajx : anchor j ≤ x := max_le hjlo hx
    have hgap : x - anchor j ≤ δ := by
      have hmax : L + (j.val : ℝ) * δ ≤ anchor j := le_max_left _ _
      change x ≤ L + ((j.val : ℝ) + 1) * δ at hjhi
      nlinarith
    have hdiff := rb_single_difference η hη x (anchor j) (hanchor j) hajx
    have hpatt := singlePrice_attains η hη (anchor j) (hanchor j)
    have hmem : price j ∈ P := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    have hrev : singleRevenue η (anchor j) ≤ menuAt η x P := by
      calc
        singleRevenue η (anchor j) = postedRevenue η (anchor j) (price j) := hpatt.2.symm
        _ ≤ postedRevenue η x (price j) := rb_posted_mono η _ hpatt.1.1.1 hajx
        _ ≤ menuAt η x P := rb_le_menu η x P (price j) hmem
    change singleRevenue η x - menuAt η x P ≤ δ
    linarith

theorem solution (ν η : Measure ℝ)
    (hν : ValidPredictions ν) (hη : ValidNoise η)
    (L U : ℝ) (hLU : L ≤ U) (hRange : ∀ᵐ x ∂ν, x ∈ Icc L U)
    (k : ℕ) (hk : 1 ≤ k) :
    segmentationLoss ν η k ≤ (U - L) / (k : ℝ) := by
  letI : IsProbabilityMeasure ν := hν.1
  letI : IsProbabilityMeasure η := hη.1
  obtain ⟨P, hP, happrox⟩ := grid_menu_approximation η hη L U k hk
  have hsingle := rb_single_integrable ν η hν hη
  have hmenu := rb_menu_integrable ν η P
  have hpoint : ∀ᵐ x ∂ν,
      singleRevenue η x - menuAt η x P ≤ (U - L) / (k : ℝ) := by
    filter_upwards [hν.2.2, hRange] with x hx hr
    exact happrox x hx hr
  have hint : (∫ x, singleRevenue η x - menuAt η x P ∂ν) ≤
      (U - L) / (k : ℝ) := by
    calc
      _ ≤ ∫ _x : ℝ, (U - L) / (k : ℝ) ∂ν :=
        integral_mono_ae (hsingle.sub hmenu) (integrable_const _) hpoint
      _ = (U - L) / (k : ℝ) := by simp
  rw [integral_sub hsingle hmenu] at hint
  change personalizedRevenue ν η - menuRevenue ν η P ≤ (U - L) / (k : ℝ) at hint
  have hsup := rb_menuRevenue_le_optimal ν η hν hη hP
  unfold segmentationLoss
  linarith
