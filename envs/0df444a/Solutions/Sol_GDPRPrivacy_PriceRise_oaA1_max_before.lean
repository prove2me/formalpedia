-- Prove2me | solution 1 for GDPRPrivacy.PriceRise.oaA1_max_before
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T19:34:03.63843+00:00
-- url     : https://prove2.me/submissions/9849b993-f705-43a0-9e13-8f5faf249f64

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


theorem fB_hi (x α q : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hq : 1 + x ≤ q) :
    profitBefore x α q = 0 := by
  unfold profitBefore; rw [before_hi x q hx0 hx1 hq]; ring

theorem fB_lo (x α q : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hq : q ≤ x - 1) :
    profitBefore x α q = q + α := by
  unfold profitBefore; rw [before_lo x q hx0 hx1 hq]; ring

theorem fB_h (x α q : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (h1 : x < q) (h2 : q < 1 + x) :
    profitBefore x α q = (q + α) * (1 + x - q) ^ 2 / 2 := by
  unfold profitBefore; rw [(eq4_demand_before x q hx0 hx1).1 h1 h2]; ring

theorem fB_l (x α q : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (h1 : x - 1 ≤ q) (h2 : q ≤ x) :
    profitBefore x α q = (q + α) * (1 - (1 - x + q) ^ 2 / 2) := by
  unfold profitBefore; rw [(eq4_demand_before x q hx0 hx1).2 h1 h2]

set_option maxHeartbeats 1000000 in
/-- Key: the claimed price is the strict global maximizer. -/
theorem before_key (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α) (q : ℝ)
    (hq : q ≠ (if α < alpha1 x then (1 + x - 2 * α) / 3
           else (2 * (x - 1) - α + beta x α) / 3)) :
    profitBefore x α q < profitBefore x α (if α < alpha1 x then (1 + x - 2 * α) / 3
           else (2 * (x - 1) - α + beta x α) / 3) := by
  have hb0 : 0 ≤ beta x α := Real.sqrt_nonneg _
  have hbsq : beta x α ^ 2 = 6 + (x + α - 1) ^ 2 := Real.sq_sqrt (by positivity)
  have hbabs : |x + α - 1| < beta x α :=
    (Real.lt_sqrt (abs_nonneg _)).2 (by rw [sq_abs]; linarith)
  set b := beta x α
  -- values at x and x - 1
  have vx : profitBefore x α x = (x + α) / 2 := by
    rw [fB_l x α x hx0 hx1 (by linarith) le_rfl]; ring
  have vx1 : profitBefore x α (x - 1) = x - 1 + α := by
    rw [fB_l x α (x - 1) hx0 hx1 le_rfl (by linarith)]; ring
  split_ifs with hA
  · have h1 : 2 * x + 2 * α < 1 := by
      unfold alpha1 at hA
      rcases max_cases ((1 - 2 * x) / 2) 0 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] at hA <;> linarith
    rw [if_pos hA] at hq
    set ps := (1 + x - 2 * α) / 3 with hps
    have hps1 : x < ps := by rw [hps]; linarith
    have hps2 : ps < 1 + x := by rw [hps]; linarith
    rw [fB_h x α ps hx0 hx1 hps1 hps2]
    -- gh(ps) - gh(p) = (1+x-2a-3p)^2 (a - 3p + 4x + 4)/54
    have key : ∀ p : ℝ, p < 1 + x → p ≠ ps →
        (p + α) * (1 + x - p) ^ 2 / 2 < (ps + α) * (1 + x - ps) ^ 2 / 2 := by
      intro p hp hne
      have hsq : 0 < (1 + x - 2 * α - 3 * p) ^ 2 := by
        refine lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ?_))
        intro h; apply hne; rw [hps]; linarith
      have : (ps + α) * (1 + x - ps) ^ 2 / 2 - (p + α) * (1 + x - p) ^ 2 / 2
          = (1 + x - 2 * α - 3 * p) ^ 2 * (α - 3 * p + 4 * x + 4) / 54 := by
        rw [hps]; ring
      have hpos : 0 < α - 3 * p + 4 * x + 4 := by linarith
      linarith [mul_pos hsq hpos]
    have hgx := key x (by linarith) (ne_of_lt hps1)
    have hglx : ∀ p, x - 1 ≤ p → p ≤ x → (p + α) * (1 - (1 - x + p) ^ 2 / 2) ≤ (x + α) / 2 := by
      intro p hp1 hp2
      have : (x + α) / 2 - (p + α) * (1 - (1 - x + p) ^ 2 / 2) =
          (x - p) * ((1 - 2 * x - 2 * α) + (x - p) * (α + x + 2 - (x - p))) / 2 := by ring
      have hu : 0 ≤ x - p := by linarith
      have hu1 : x - p ≤ 1 := by linarith
      nlinarith [mul_nonneg hu (mul_nonneg hu (by linarith : (0:ℝ) ≤ α + x + 2 - (x - p)))]
    have gx_eq : (x + α) * (1 + x - x) ^ 2 / 2 = (x + α) / 2 := by ring
    rcases lt_or_ge q (x - 1) with hq1 | hq1
    · rw [fB_lo x α q hx0 hx1 hq1.le]
      have := hglx (x - 1) le_rfl (by linarith)
      have e : (x - 1 + α) * (1 - (1 - x + (x - 1)) ^ 2 / 2) = x - 1 + α := by ring
      linarith
    rcases le_or_gt q x with hq2 | hq2
    · rw [fB_l x α q hx0 hx1 hq1 hq2]
      linarith [hglx q hq1 hq2]
    rcases lt_or_ge q (1 + x) with hq3 | hq3
    · rw [fB_h x α q hx0 hx1 hq2 hq3]; exact key q hq3 hq
    · rw [fB_hi x α q hx0 hx1 hq3]
      have : 0 < (ps + α) * (1 + x - ps) ^ 2 / 2 := by
        have : 0 < ps + α := by linarith
        have : 0 < 1 + x - ps := by linarith
        positivity
      linarith
  · rw [not_lt] at hA
    have h1 : 1 ≤ 2 * x + 2 * α := by
      have := le_trans (le_max_left _ _) hA; linarith
    rw [if_neg (not_lt.2 hA)] at hq
    set ps := (2 * (x - 1) - α + b) / 3 with hps
    have hb1 : x + α - 1 < b := lt_of_le_of_lt (le_abs_self _) hbabs
    have hb1' : -(x + α - 1) < b := lt_of_le_of_lt (neg_le_abs _) hbabs
    have hb2 : b ≤ x + 2 + α :=
      (pow_le_pow_iff_left₀ hb0 (by linarith) two_ne_zero).1 (by nlinarith)
    have hps1 : x - 1 ≤ ps := by rw [hps]; linarith
    have hps2 : ps ≤ x := by rw [hps]; linarith
    rw [fB_l x α ps hx0 hx1 hps1 hps2]
    have key : ∀ p : ℝ, x - 1 ≤ p →
        (ps + α) * (1 - (1 - x + ps) ^ 2 / 2) - (p + α) * (1 - (1 - x + p) ^ 2 / 2)
          = (p - ps) ^ 2 * (p + (2 * (1 - x) + α + 2 * b) / 3) / 2 := by
      intro p _
      rw [hps]; linear_combination (α / 18 - b / 18 + p / 6 - x / 9 + 1 / 9) * hbsq
    have fac : ∀ p : ℝ, x - 1 ≤ p → 0 < p + (2 * (1 - x) + α + 2 * b) / 3 := by
      intro p hp; linarith
    have hgx : (x + α) / 2 ≤ (ps + α) * (1 - (1 - x + ps) ^ 2 / 2) := by
      have := key x (by linarith)
      have h3 : (x + α) * (1 - (1 - x + x) ^ 2 / 2) = (x + α) / 2 := by ring
      linarith [mul_nonneg (sq_nonneg (x - ps)) (fac x (by linarith)).le]
    rcases lt_or_ge q (x - 1) with hq1 | hq1
    · rw [fB_lo x α q hx0 hx1 hq1.le]
      have := key (x - 1) le_rfl
      have e : (x - 1 + α) * (1 - (1 - x + (x - 1)) ^ 2 / 2) = x - 1 + α := by ring
      linarith [mul_nonneg (sq_nonneg (x - 1 - ps)) (fac (x - 1) le_rfl).le]
    rcases le_or_gt q x with hq2 | hq2
    · rw [fB_l x α q hx0 hx1 hq1 hq2]
      have := key q hq1
      have hsq : 0 < (q - ps) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 hq)))
      linarith [mul_pos hsq (fac q hq1)]
    rcases lt_or_ge q (1 + x) with hq3 | hq3
    · rw [fB_h x α q hx0 hx1 hq2 hq3]
      have hu : 0 < q - x := by linarith
      have hu1 : q - x < 1 := by linarith
      have hR : 0 < (α + x) * (2 - (q - x)) - (1 - (q - x)) ^ 2 := by
        nlinarith [mul_pos hu (by linarith : (0:ℝ) < 3 / 2 - (q - x)),
          mul_nonneg (by linarith : (0:ℝ) ≤ x + α - 1 / 2) (by linarith : (0:ℝ) ≤ 2 - (q - x))]
      have : (x + α) / 2 - (q + α) * (1 + x - q) ^ 2 / 2
          = (q - x) * ((α + x) * (2 - (q - x)) - (1 - (q - x)) ^ 2) / 2 := by ring
      linarith [mul_pos hu hR]
    · rw [fB_hi x α q hx0 hx1 hq3]
      linarith

theorem solution (x α : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hα : 0 ≤ α) (p : ℝ) :
    IsMaxOn (profitBefore x α) Set.univ p ↔
      p = (if α < alpha1 x then (1 + x - 2 * α) / 3
           else (2 * (x - 1) - α + beta x α) / 3) := by
  constructor
  · intro h
    by_contra hne
    have := before_key x α hx0 hx1 hα p hne
    have h2 := h (Set.mem_univ (if α < alpha1 x then (1 + x - 2 * α) / 3
           else (2 * (x - 1) - α + beta x α) / 3))
    simp only [Set.mem_setOf_eq] at h2
    linarith
  · rintro rfl
    intro q _
    simp only [Set.mem_setOf_eq]
    by_cases hq : q = (if α < alpha1 x then (1 + x - 2 * α) / 3
           else (2 * (x - 1) - α + beta x α) / 3)
    · rw [hq]
    · exact (before_key x α hx0 hx1 hα q hq).le
