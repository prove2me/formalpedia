-- Prove2me | solution 1 for GDPRPrivacy.PriceRise.oaA2_max_after
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:36:44.77974+00:00
-- url     : https://prove2.me/submissions/106d7c8b-b252-48a6-85e0-9a2ef3369394

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model
import Theorems.Thm_GDPRPrivacy_PriceRise_eq4_demand_before
import Theorems.Thm_GDPRPrivacy_PriceRise_eq5_demand_in
import Theorems.Thm_GDPRPrivacy_PriceRise_eq6_demand_out

open MeasureTheory GDPRPrivacy.PriceRise




theorem vol_sq : volume typeSquare = 1 := by
  rw [typeSquare, Measure.volume_eq_prod, Measure.prod_prod]; simp [Real.volume_Icc]

theorem toReal_mono_sq {S T : Set (ℝ × ℝ)} (hST : S ⊆ T) (hT : T ⊆ typeSquare) :
    (volume S).toReal ≤ (volume T).toReal :=
  ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (vol_sq ▸ measure_mono hT))
    (measure_mono hST)

theorem toReal_le_one {S : Set (ℝ × ℝ)} (hS : S ⊆ typeSquare) : (volume S).toReal ≤ 1 := by
  have := toReal_mono_sq hS subset_rfl
  rwa [vol_sq, ENNReal.toReal_one] at this

theorem before_anti (x : ℝ) {p p' : ℝ} (h : p ≤ p') : demandBefore x p' ≤ demandBefore x p := by
  unfold demandBefore
  refine toReal_mono_sq ?_ (fun q hq => hq.1)
  intro q ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  unfold utilS at *; linarith

theorem in_anti (x : ℝ) {p p' : ℝ} (h : p ≤ p') : demandIn x p' ≤ demandIn x p := by
  unfold demandIn
  refine toReal_mono_sq ?_ (fun q hq => hq.1)
  intro q ⟨h1, h2, h3⟩
  exact ⟨h1, by linarith, h3⟩

theorem out_anti (x : ℝ) {p p' : ℝ} (h : p ≤ p') : demandOut x p' ≤ demandOut x p := by
  unfold demandOut
  refine toReal_mono_sq ?_ (fun q hq => hq.1)
  intro q ⟨h1, h2, h3⟩
  exact ⟨h1, by linarith, h3⟩

theorem before_le_one (x p : ℝ) : demandBefore x p ≤ 1 := toReal_le_one (fun q hq => hq.1)

theorem in_le (x p : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : demandIn x p ≤ x := by
  unfold demandIn
  have hsub : optInSet x p ⊆ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) x := by
    intro q ⟨⟨h1, h2⟩, _, h4⟩
    exact ⟨h1, h2.1, h4⟩
  have hT : Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) x ⊆ typeSquare := by
    intro q ⟨h1, h2⟩
    exact ⟨h1, h2.1, by linarith [h2.2]⟩
  have := toReal_mono_sq hsub hT
  rw [Measure.volume_eq_prod, Measure.prod_prod] at this
  simp [Real.volume_Icc] at this
  rw [ENNReal.toReal_ofReal hx0.le] at this
  simpa [demandIn, Measure.volume_eq_prod] using this

/-- squeeze: a quantity in `[0,1]` bounded by `t^2/2` for all small `t > 0` vanishes. -/
theorem squeeze (D c : ℝ) (hc : 0 < c) (h0 : 0 ≤ D) (h1 : D ≤ 1)
    (h : ∀ t, 0 < t → t < c → D ≤ t ^ 2 / 2) : D = 0 := by
  by_contra hne
  have hD : 0 < D := lt_of_le_of_ne h0 (Ne.symm hne)
  set t := min D c / 2 with ht
  have ht0 : 0 < t := by positivity
  have htc : t < c := by have := min_le_right D c; linarith
  have htD : t ≤ D / 2 := by have := min_le_left D c; linarith
  have := h t ht0 htc
  nlinarith

theorem before_hi (x p : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hp : 1 + x ≤ p) :
    demandBefore x p = 0 := by
  refine squeeze _ 1 one_pos ENNReal.toReal_nonneg (before_le_one x p) (fun t ht0 ht1 => ?_)
  have e := (eq4_demand_before x (1 + x - t) hx0 hx1).1 (by linarith) (by linarith)
  have := before_anti x (show 1 + x - t ≤ p by linarith)
  rw [e] at this; nlinarith

theorem before_lo (x p : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hp : p ≤ x - 1) :
    demandBefore x p = 1 := by
  have e := (eq4_demand_before x (x - 1) hx0 hx1).2 le_rfl (by linarith)
  have := before_anti x hp
  rw [e] at this
  linarith [before_le_one x p]

theorem in_hi (x p : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hp : 1 + x ≤ p) :
    demandIn x p = 0 := by
  refine squeeze _ x hx0 ENNReal.toReal_nonneg (by linarith [in_le x p hx0 hx1])
    (fun t ht0 ht1 => ?_)
  have e := (eq5_demand_in x (1 + x - t) hx0 hx1).1 (by linarith) (by linarith)
  have := in_anti x (show 1 + x - t ≤ p by linarith)
  rw [e] at this; nlinarith

theorem out_hi (x p : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hp : 1 + x ≤ p) :
    demandOut x p = 0 := by
  have e := (eq6_demand_out x (1 + x / 2) hx0 hx1).1 (by linarith) (by linarith)
  have := out_anti x (show 1 + x / 2 ≤ p by linarith)
  rw [e] at this
  exact le_antisymm this ENNReal.toReal_nonneg


theorem fA_hi (x α q : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hq : 1 + x ≤ q) :
    profitAfter x α q = 0 := by
  unfold profitAfter demandAfter
  rw [in_hi x q hx0 hx1 hq, out_hi x q hx0 hx1 hq]; ring

theorem fA_1 (x α q : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (h1 : 1 < q) (h2 : q < 1 + x) :
    profitAfter x α q = (q + α) * (1 + x - q) ^ 2 / 2 := by
  unfold profitAfter demandAfter
  rw [(eq5_demand_in x q hx0 hx1).1 h1 h2, (eq6_demand_out x q hx0 hx1).1 h1 h2]; ring

theorem fA_h (x α q : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (h1 : x < q) (h2 : q ≤ 1) :
    profitAfter x α q = q * (x ^ 2 / 2 + 1 - q) + α * (x ^ 2 / 2 + x - x * q) := by
  unfold profitAfter demandAfter
  rw [(eq5_demand_in x q hx0 hx1).2.1 h1 h2,
    (eq6_demand_out x q hx0 hx1).2 (by linarith) h2]; ring

theorem fA_l (x α q : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (h1 : 0 ≤ q) (h2 : q ≤ x) :
    profitAfter x α q = q * (x - q ^ 2 / 2 + (1 - x) * (1 - q)) + α * (x - q ^ 2 / 2) := by
  unfold profitAfter demandAfter
  rw [(eq5_demand_in x q hx0 hx1).2.2 h1 h2,
    (eq6_demand_out x q hx0 hx1).2 h1 (by linarith)]

theorem fA_lo (x α q : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α) (hq : q < 0) :
    profitAfter x α q ≤ q + α * x := by
  unfold profitAfter demandAfter
  have e1 := (eq5_demand_in x 0 hx0 hx1).2.2 le_rfl hx0.le
  have e2 := (eq6_demand_out x 0 hx0 hx1).2 le_rfl zero_le_one
  have m1 := in_anti x hq.le
  have m2 := out_anti x hq.le
  rw [e1] at m1; rw [e2] at m2
  have hu := in_le x q hx0 hx1
  have hD : 1 ≤ demandIn x q + demandOut x q := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hu hα]

set_option maxHeartbeats 1000000 in
/-- Key: the claimed price is the strict global maximizer. -/
theorem after_key (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α) (q : ℝ)
    (hq : q ≠ (if α < alpha2 x then (2 * (1 - α * x) + x ^ 2) / 4
           else (Gamma x α - (2 - 2 * x + α)) / 3)) :
    profitAfter x α q < profitAfter x α (if α < alpha2 x then (2 * (1 - α * x) + x ^ 2) / 4
           else (Gamma x α - (2 - 2 * x + α)) / 3) := by
  have hG0 : 0 ≤ Gamma x α := Real.sqrt_nonneg _
  have hGsq : Gamma x α ^ 2 = 6 + (2 - 2 * x + α) ^ 2 := Real.sq_sqrt (by positivity)
  have hGabs : |2 - 2 * x + α| < Gamma x α :=
    (Real.lt_sqrt (abs_nonneg _)).2 (by rw [sq_abs]; linarith)
  set G := Gamma x α
  -- generic shape facts
  have fh_eq : ∀ p : ℝ, (2 * (1 - α * x) + x ^ 2) / 4 * (x ^ 2 / 2 + 1 - (2 * (1 - α * x) + x ^ 2) / 4)
      + α * (x ^ 2 / 2 + x - x * ((2 * (1 - α * x) + x ^ 2) / 4))
      - (p * (x ^ 2 / 2 + 1 - p) + α * (x ^ 2 / 2 + x - x * p))
      = (p - (2 * (1 - α * x) + x ^ 2) / 4) ^ 2 := by intro p; ring
  have fhx : ∀ p : ℝ, x * (x ^ 2 / 2 + 1 - x) + α * (x ^ 2 / 2 + x - x * x)
      - (p * (x ^ 2 / 2 + 1 - p) + α * (x ^ 2 / 2 + x - x * p))
      = (p - x) * (2 * p - (2 - 2 * x + x ^ 2 - 2 * α * x)) / 2 := by intro p; ring
  have flx : ∀ p : ℝ, x * (x - x ^ 2 / 2 + (1 - x) * (1 - x)) + α * (x - x ^ 2 / 2)
      - (p * (x - p ^ 2 / 2 + (1 - x) * (1 - p)) + α * (x - p ^ 2 / 2))
      = (x - p) * ((2 - 4 * x + x ^ 2 - 2 * α * x) + (x - p) * (α + p + 2)) / 2 := by
    intro p; ring
  have f1 : ∀ p : ℝ, (1 + α) * (1 + x - 1) ^ 2 / 2 - (p + α) * (1 + x - p) ^ 2 / 2
      = (p - 1) * (α * (2 * x + 1 - p) + (p - (p - x) ^ 2)) / 2 := by intro p; ring
  have vh1 : profitAfter x α 1 = (1 + α) * (1 + x - 1) ^ 2 / 2 := by
    rw [fA_h x α 1 hx0 hx1 hx1 le_rfl]; ring
  have vhx_l : x * (x ^ 2 / 2 + 1 - x) + α * (x ^ 2 / 2 + x - x * x)
      = x * (x - x ^ 2 / 2 + (1 - x) * (1 - x)) + α * (x - x ^ 2 / 2) := by ring
  -- region (1, 1+x): f q < f 1
  have reg1 : ∀ p, 1 < p → p < 1 + x → (p + α) * (1 + x - p) ^ 2 / 2 < (1 + α) * (1 + x - 1) ^ 2 / 2 := by
    intro p hp1 hp2
    have hp : 0 < p - 1 := by linarith
    have hS : 0 < α * (2 * x + 1 - p) + (p - (p - x) ^ 2) := by
      have : 0 ≤ α * (2 * x + 1 - p) := mul_nonneg hα (by linarith)
      nlinarith
    have := f1 p
    linarith [mul_pos hp hS]
  split_ifs with hA
  · have h2 : 2 * x * α < 2 - 4 * x + x ^ 2 := by
      unfold alpha2 at hA
      rcases max_cases ((2 - 4 * x + x ^ 2) / (2 * x)) 0 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hA
      · rw [lt_div_iff₀ (by positivity)] at hA; linarith
      · linarith
    rw [if_pos hA] at hq
    set ps := (2 * (1 - α * x) + x ^ 2) / 4 with hps
    have hps1 : x < ps := by rw [hps]; nlinarith
    have hps2 : ps ≤ 1 := by rw [hps]; nlinarith [mul_nonneg hα hx0.le]
    rw [fA_h x α ps hx0 hx1 hps1 hps2]
    have hxlt : x * (x ^ 2 / 2 + 1 - x) + α * (x ^ 2 / 2 + x - x * x) <
        ps * (x ^ 2 / 2 + 1 - ps) + α * (x ^ 2 / 2 + x - x * ps) := by
      have := fh_eq x
      have : 0 < (x - ps) ^ 2 := by
        refine lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ?_)); linarith
      linarith
    have hl : ∀ p, 0 ≤ p → p ≤ x → p * (x - p ^ 2 / 2 + (1 - x) * (1 - p)) + α * (x - p ^ 2 / 2)
        ≤ x * (x - x ^ 2 / 2 + (1 - x) * (1 - x)) + α * (x - x ^ 2 / 2) := by
      intro p hp0 hpx
      have := flx p
      have hu : 0 ≤ x - p := by linarith
      have : 0 ≤ (x - p) * ((2 - 4 * x + x ^ 2 - 2 * α * x) + (x - p) * (α + p + 2)) :=
        mul_nonneg hu (by nlinarith [mul_nonneg hu (by linarith : (0:ℝ) ≤ α + p + 2)])
      linarith
    have h1le : (1 + α) * (1 + x - 1) ^ 2 / 2 ≤ ps * (x ^ 2 / 2 + 1 - ps) + α * (x ^ 2 / 2 + x - x * ps) := by
      have := fh_eq 1; have := sq_nonneg (1 - ps)
      have e : (1 + α) * (1 + x - 1) ^ 2 / 2 = 1 * (x ^ 2 / 2 + 1 - 1) + α * (x ^ 2 / 2 + x - x * 1) := by ring
      linarith
    rcases lt_or_ge q 0 with hq0 | hq0
    · have := fA_lo x α q hx0 hx1 hα hq0
      have := hl 0 le_rfl hx0.le
      have e : (0:ℝ) * (x - 0 ^ 2 / 2 + (1 - x) * (1 - 0)) + α * (x - 0 ^ 2 / 2) = α * x := by ring
      linarith
    rcases le_or_gt q x with hqx | hqx
    · rw [fA_l x α q hx0 hx1 hq0 hqx]
      linarith [hl q hq0 hqx]
    rcases le_or_gt q 1 with hq1 | hq1
    · rw [fA_h x α q hx0 hx1 hqx hq1]
      have := fh_eq q
      have : 0 < (q - ps) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hq)))
      linarith
    rcases lt_or_ge q (1 + x) with hq2 | hq2
    · rw [fA_1 x α q hx0 hx1 hq1 hq2]
      linarith [reg1 q hq1 hq2]
    · rw [fA_hi x α q hx0 hx1 hq2]
      have : 0 < (1 + α) * (1 + x - 1) ^ 2 / 2 := by
        have : 0 < 1 + α := by linarith
        have : 0 < (1 + x - 1) ^ 2 := by nlinarith
        positivity
      linarith
  · rw [not_lt] at hA
    have h2 : 2 - 4 * x + x ^ 2 ≤ 2 * x * α := by
      have := le_trans (le_max_left _ _) hA
      rw [div_le_iff₀ (by positivity)] at this; linarith
    rw [if_neg (not_lt.2 hA)] at hq
    set ps := (G - (2 - 2 * x + α)) / 3 with hps
    have hG1 : 2 - 2 * x + α < G := lt_of_le_of_lt (le_abs_self _) hGabs
    have hG2 : G ≤ 2 + x + α :=
      (pow_le_pow_iff_left₀ hG0 (by linarith) two_ne_zero).1 (by nlinarith)
    have hps1 : 0 ≤ ps := by rw [hps]; linarith
    have hps2 : ps ≤ x := by rw [hps]; linarith
    rw [fA_l x α ps hx0 hx1 hps1 hps2]
    have key : ∀ p : ℝ,
        ps * (x - ps ^ 2 / 2 + (1 - x) * (1 - ps)) + α * (x - ps ^ 2 / 2)
          - (p * (x - p ^ 2 / 2 + (1 - x) * (1 - p)) + α * (x - p ^ 2 / 2))
          = (p - ps) ^ 2 * (p + (2 * G + 2 - 2 * x + α) / 3) / 2 := by
      intro p
      rw [hps]; linear_combination (-G / 18 + α / 18 + p / 6 - x / 9 + 1 / 9) * hGsq
    have fac : ∀ p : ℝ, 0 ≤ p → 0 < p + (2 * G + 2 - 2 * x + α) / 3 := by
      intro p hp; linarith
    have hge : ∀ p : ℝ, 0 ≤ p →
        p * (x - p ^ 2 / 2 + (1 - x) * (1 - p)) + α * (x - p ^ 2 / 2) ≤
        ps * (x - ps ^ 2 / 2 + (1 - x) * (1 - ps)) + α * (x - ps ^ 2 / 2) := by
      intro p hp
      have := key p
      linarith [mul_nonneg (sq_nonneg (p - ps)) (fac p hp).le]
    have hxle := hge x hx0.le
    have hfh : ∀ p, x < p → p * (x ^ 2 / 2 + 1 - p) + α * (x ^ 2 / 2 + x - x * p) <
        x * (x ^ 2 / 2 + 1 - x) + α * (x ^ 2 / 2 + x - x * x) := by
      intro p hp
      have := fhx p
      have : 0 < (p - x) * (2 * p - (2 - 2 * x + x ^ 2 - 2 * α * x)) :=
        mul_pos (by linarith) (by linarith)
      linarith
    rcases lt_or_ge q 0 with hq0 | hq0
    · have := fA_lo x α q hx0 hx1 hα hq0
      have := hge 0 le_rfl
      have e : (0:ℝ) * (x - 0 ^ 2 / 2 + (1 - x) * (1 - 0)) + α * (x - 0 ^ 2 / 2) = α * x := by ring
      linarith
    rcases le_or_gt q x with hqx | hqx
    · rw [fA_l x α q hx0 hx1 hq0 hqx]
      have := key q
      have hsq : 0 < (q - ps) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hq)))
      linarith [mul_pos hsq (fac q hq0)]
    rcases le_or_gt q 1 with hq1 | hq1
    · rw [fA_h x α q hx0 hx1 hqx hq1]
      linarith [hfh q hqx]
    have h1x := hfh 1 hx1
    have e1 : (1 + α) * (1 + x - 1) ^ 2 / 2 = 1 * (x ^ 2 / 2 + 1 - 1) + α * (x ^ 2 / 2 + x - x * 1) := by ring
    rcases lt_or_ge q (1 + x) with hq2 | hq2
    · rw [fA_1 x α q hx0 hx1 hq1 hq2]
      linarith [reg1 q hq1 hq2]
    · rw [fA_hi x α q hx0 hx1 hq2]
      have : 0 < x * (x - x ^ 2 / 2 + (1 - x) * (1 - x)) + α * (x - x ^ 2 / 2) := by
        have : 0 < x - x ^ 2 / 2 + (1 - x) * (1 - x) := by nlinarith
        have : 0 ≤ x - x ^ 2 / 2 := by nlinarith
        positivity
      linarith

theorem solution (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α) (p : ℝ) :
    IsMaxOn (profitAfter x α) Set.univ p ↔
      p = (if α < alpha2 x then (2 * (1 - α * x) + x ^ 2) / 4
           else (Gamma x α - (2 - 2 * x + α)) / 3) := by
  constructor
  · intro h
    by_contra hne
    have := after_key x α hx0 hx1 hα p hne
    have h2 := h (Set.mem_univ (if α < alpha2 x then (2 * (1 - α * x) + x ^ 2) / 4
           else (Gamma x α - (2 - 2 * x + α)) / 3))
    simp only [Set.mem_setOf_eq] at h2
    linarith
  · rintro rfl
    intro q _
    simp only [Set.mem_setOf_eq]
    by_cases hq : q = (if α < alpha2 x then (2 * (1 - α * x) + x ^ 2) / 4
           else (Gamma x α - (2 - 2 * x + α)) / 3)
    · rw [hq]
    · exact (after_key x α hx0 hx1 hα q hq).le
