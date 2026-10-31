-- Prove2me | solution 1 for FBMSP.lemma1_pricing_geometry
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T12:16:35.058645+00:00
-- url     : https://prove2.me/submissions/0470c1b7-fdb4-4a8c-a9a4-1f6a73c194df

import Theorems.Thm_FBMSP_singlePrice_attains

open MeasureTheory Set FBMSP

private lemma geometry_revenue_nonneg (η : Measure ℝ) (hnoise : ValidNoise η)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ singleRevenue η x := by
  obtain ⟨hp, hr⟩ := singlePrice_attains η hnoise x hx
  rw [← hr]
  exact mul_nonneg hp.1.1 ENNReal.toReal_nonneg

private lemma geometry_margin_value (η : Measure ℝ) (hnoise : ValidNoise η)
    (x : ℝ) (hx : 0 ≤ x) :
    singleRevenue η x = (x + margin η x) * survival η (margin η x) := by
  rw [← (singlePrice_attains η hnoise x hx).2]
  unfold postedRevenue margin
  ring

private lemma geometry_affine_le (η : Measure ℝ) (hnoise : ValidNoise η)
    (x θ : ℝ) (hx : 0 ≤ x) :
    (x + θ) * survival η θ ≤ singleRevenue η x := by
  by_cases hprice : 0 ≤ x + θ
  · have h := (singlePrice_attains η hnoise x hx).1.1.2 (x + θ) hprice
    rw [(singlePrice_attains η hnoise x hx).2] at h
    simpa only [postedRevenue, add_sub_cancel_left] using h
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hprice)
      ENNReal.toReal_nonneg).trans (geometry_revenue_nonneg η hnoise x hx)

private lemma geometry_survival_antitone (η : Measure ℝ) [IsProbabilityMeasure η] :
    Antitone (survival η) := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top η (Ici a))
    (measure_mono (Ici_subset_Ici.mpr hab))

private lemma geometry_survival_le_one (η : Measure ℝ) [IsProbabilityMeasure η] (t : ℝ) :
    survival η t ≤ 1 := by
  exact measureReal_le_one

theorem solution (η : MeasureTheory.Measure ℝ)
    (hnoise : ValidNoise η) :
    AntitoneOn (margin η) (Set.Ioi (0 : ℝ)) ∧
    (∀ x₁ x₂ : ℝ, 0 < x₁ → x₁ < x₂ →
      survival η (margin η x₁) * (x₂ - x₁) ≤
          singleRevenue η x₂ - singleRevenue η x₁ ∧
        singleRevenue η x₂ - singleRevenue η x₁ ≤
          survival η (margin η x₂) * (x₂ - x₁)) ∧
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (singleRevenue η) ∧
    ContinuousOn (singleRevenue η) (Set.Ioi (0 : ℝ)) ∧
    MonotoneOn (singleRevenue η) (Set.Ioi (0 : ℝ)) ∧
    LipschitzOnWith 1 (singleRevenue η) (Set.Ioi (0 : ℝ)) := by
  letI : IsProbabilityMeasure η := hnoise.1
  have hsecant : ∀ x y : ℝ, 0 < x → x < y →
      survival η (margin η x) * (y - x) ≤ singleRevenue η y - singleRevenue η x ∧
      singleRevenue η y - singleRevenue η x ≤ survival η (margin η y) * (y - x) := by
    intro x y hx hxy
    have hy : 0 ≤ y := le_of_lt (lt_trans hx hxy)
    have hlow := geometry_affine_le η hnoise y (margin η x) hy
    have hupp := geometry_affine_le η hnoise x (margin η y) (le_of_lt hx)
    have hxval := geometry_margin_value η hnoise x (le_of_lt hx)
    have hyval := geometry_margin_value η hnoise y hy
    constructor
    · nlinarith only [hlow, hxval]
    · nlinarith only [hupp, hyval]
  have hmargin : AntitoneOn (margin η) (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    rcases eq_or_lt_of_le hxy with heq | hlt
    · simpa [heq]
    by_contra hbad
    have hθ : margin η x < margin η y := lt_of_not_ge hbad
    have hsurv : survival η (margin η y) ≤ survival η (margin η x) :=
      geometry_survival_antitone η (le_of_lt hθ)
    have hsec := hsecant x y hx hlt
    have hmul := mul_le_mul_of_nonneg_right hsurv (sub_nonneg.mpr hxy)
    have hvalue : singleRevenue η y = singleRevenue η x +
        survival η (margin η x) * (y - x) := by
      linarith [hsec.1, hsec.2]
    obtain ⟨hpx, _⟩ := singlePrice_attains η hnoise x (le_of_lt hx)
    obtain ⟨hpy, hry⟩ := singlePrice_attains η hnoise y (le_of_lt hy)
    have hq : 0 ≤ y + margin η x := by
      have hp := hpx.1.1
      unfold margin
      linarith
    have hqlt : y + margin η x < singlePrice η y := by
      unfold margin at hθ ⊢
      linarith
    have hqr : postedRevenue η y (y + margin η x) = singleRevenue η y := by
      calc
        postedRevenue η y (y + margin η x) =
            (y + margin η x) * survival η (margin η x) := by
              simp only [postedRevenue, add_sub_cancel_left]
        _ = singleRevenue η x + survival η (margin η x) * (y - x) := by
              rw [geometry_margin_value η hnoise x (le_of_lt hx)]
              ring
        _ = singleRevenue η y := hvalue.symm
    have hqopt : IsOptimalPrice η y (y + margin η x) := by
      refine ⟨hq, ?_⟩
      intro q hq'
      calc
        postedRevenue η y q ≤ postedRevenue η y (singlePrice η y) := hpy.1.2 q hq'
        _ = singleRevenue η y := hry
        _ = postedRevenue η y (y + margin η x) := hqr.symm
    exact (not_le_of_gt hqlt) (hpy.2 _ hqopt)
  have hconvex : ConvexOn ℝ (Ioi (0 : ℝ)) (singleRevenue η) := by
    refine ⟨convex_Ioi _, ?_⟩
    intro x hx y hy a b ha hb hab
    let z : ℝ := a * x + b * y
    have hz : 0 ≤ z := add_nonneg (mul_nonneg ha (le_of_lt hx))
      (mul_nonneg hb (le_of_lt hy))
    have hleft := geometry_affine_le η hnoise x (margin η z) (le_of_lt hx)
    have hright := geometry_affine_le η hnoise y (margin η z) (le_of_lt hy)
    change singleRevenue η z ≤ a * singleRevenue η x + b * singleRevenue η y
    rw [geometry_margin_value η hnoise z hz]
    calc
      (z + margin η z) * survival η (margin η z) =
          (a * x + b * y + (a + b) * margin η z) * survival η (margin η z) := by
            rw [hab]
            simp only [one_mul, z]
      _ = a * ((x + margin η z) * survival η (margin η z)) +
          b * ((y + margin η z) * survival η (margin η z)) := by ring
      _ ≤ a * singleRevenue η x + b * singleRevenue η y :=
          add_le_add (mul_le_mul_of_nonneg_left hleft ha)
            (mul_le_mul_of_nonneg_left hright hb)
  have hsteps : ∀ x y : ℝ, 0 < x → 0 < y → x ≤ y →
      0 ≤ singleRevenue η y - singleRevenue η x ∧
      singleRevenue η y - singleRevenue η x ≤ y - x := by
    intro x y hx hy hxy
    rcases eq_or_lt_of_le hxy with heq | hlt
    · subst y
      simp
    have hs := hsecant x y hx hlt
    have hlo : 0 ≤ survival η (margin η x) * (y - x) :=
      mul_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr hxy)
    have hup := mul_le_mul_of_nonneg_right (geometry_survival_le_one η (margin η y))
      (sub_nonneg.mpr hxy)
    constructor <;> linarith [hs.1, hs.2]
  have hmono : MonotoneOn (singleRevenue η) (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    exact sub_nonneg.mp (hsteps x y hx hy hxy).1
  have hlip : LipschitzOnWith 1 (singleRevenue η) (Ioi (0 : ℝ)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rcases le_total x y with hxy | hyx
    · have hs := hsteps x y hx hy hxy
      rw [abs_of_nonpos (sub_nonpos.mpr (sub_nonneg.mp hs.1)),
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith [hs.2]
    · have hs := hsteps y x hy hx hyx
      rw [abs_of_nonneg hs.1, abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact hs.2
  exact ⟨hmargin, hsecant, hconvex, hlip.continuousOn, hmono, hlip⟩
