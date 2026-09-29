-- Prove2me | solution 1 for BanditAlgorithm.adversarial_linear_bandit_ftrl_unit_ball_regret_untuned
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T05:05:28.043711+00:00
-- url     : https://prove2.me/submissions/5d536ad8-5bed-421a-9417-8d4578224ac1

import Definitions.Def_OnlineLinearOptimization
import Theorems.Thm_BanditAlgorithm_ftrl_regret_bound
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

open RealInnerProductSpace MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Filter

namespace BanditAlgorithm

private lemma radialObjective_min
    {q r x : ℝ} (hq : 0 ≤ q) (hr0 : 0 < r) (hr1 : r < 1)
    (hx0 : 0 ≤ x) (hxr : x ≤ r) :
    let s := min r (q / (1 + q));
    -q * x - Real.log (1 - x) - x ≥
      -q * s - Real.log (1 - s) - s := by
  dsimp
  have hqden : 0 < 1 + q := by linarith
  have hs00 : 0 ≤ q / (1 + q) := div_nonneg hq (le_of_lt hqden)
  have hs01 : q / (1 + q) < 1 := by
    rw [div_lt_one hqden]
    linarith
  by_cases hcase : r ≤ q / (1 + q)
  · rw [min_eq_left hcase]
    have hxr1 : 0 < 1 - x := by linarith
    have hrr1 : 0 < 1 - r := by linarith
    have hz : 0 < (1 - x) / (1 - r) := div_pos hxr1 hrr1
    have hlog := Real.log_le_sub_one_of_pos hz
    rw [Real.log_div (ne_of_gt hxr1) (ne_of_gt hrr1)] at hlog
    have hcoef : 1 / (1 - r) ≤ 1 + q := by
      rw [le_div_iff₀ hqden] at hcase
      rw [div_le_iff₀ hrr1]
      nlinarith
    have hdiff : 0 ≤ r - x := sub_nonneg.mpr hxr
    have hmul : (r - x) / (1 - r) ≤ (1 + q) * (r - x) := by
      simpa [div_eq_mul_inv, mul_comm] using
        (mul_le_mul_of_nonneg_right hcoef hdiff)
    have hratio :
        (1 - x) / (1 - r) - 1 = (r - x) / (1 - r) := by
      field_simp [ne_of_gt hrr1]
      ring
    have hdiffobj :
        0 ≤ (-q * x - Real.log (1 - x) - x) -
          (-q * r - Real.log (1 - r) - r) := by
      calc
        (-q * x - Real.log (1 - x) - x) -
          (-q * r - Real.log (1 - r) - r) =
          (1 + q) * (r - x) -
            (Real.log (1 - x) - Real.log (1 - r)) := by ring
        _ ≥ (r - x) / (1 - r) -
            (Real.log (1 - x) - Real.log (1 - r)) := by linarith
        _ ≥ 0 := by rw [← hratio]; exact sub_nonneg.mpr hlog
    linarith
  · have hcase' : q / (1 + q) ≤ r := le_of_not_ge hcase
    rw [min_eq_right hcase']
    let s := q / (1 + q)
    have hs0 : 0 ≤ s := hs00
    have hs1 : s < 1 := hs01
    have hxs1 : 0 < 1 - x := by linarith
    have hss1 : 0 < 1 - s := by linarith
    have hssne : 1 - s ≠ 0 := ne_of_gt hss1
    have hz : 0 < (1 - x) / (1 - s) := div_pos hxs1 hss1
    have hlog := Real.log_le_sub_one_of_pos hz
    rw [Real.log_div (ne_of_gt hxs1) (ne_of_gt hss1)] at hlog
    have hqrel : (1 + q) * (1 - s) = 1 := by
      dsimp [s]
      field_simp
      ring
    have hratio :
        (1 - x) / (1 - s) - 1 = (s - x) / (1 - s) := by
      field_simp [hssne]
      ring
    have hlin :
        (1 + q) * (s - x) = (1 - x) / (1 - s) - 1 := by
      rw [hratio, eq_div_iff hssne]
      nlinarith
    have hdiffobj :
        0 ≤ (-q * x - Real.log (1 - x) - x) -
          (-q * s - Real.log (1 - s) - s) := by
      calc
        (-q * x - Real.log (1 - x) - x) -
            (-q * s - Real.log (1 - s) - s) =
            (1 + q) * (s - x) -
              (Real.log (1 - x) - Real.log (1 - s)) := by ring
        _ = ((1 - x) / (1 - s) - 1) -
              (Real.log (1 - x) - Real.log (1 - s)) := by rw [hlin]
        _ ≥ 0 := sub_nonneg.mpr hlog
    dsimp [s] at hdiffobj
    linarith

private lemma radialObjective_eq_min_iff
    {q r x : ℝ} (hq : 0 ≤ q) (hr0 : 0 < r) (hr1 : r < 1)
    (hx0 : 0 ≤ x) (hxr : x ≤ r) :
    let s := min r (q / (1 + q));
    (-q * x - Real.log (1 - x) - x =
      -q * s - Real.log (1 - s) - s) ↔ x = s := by
  dsimp
  have hqden : 0 < 1 + q := by linarith
  have hs01 : q / (1 + q) < 1 := by
    rw [div_lt_one hqden]
    linarith
  constructor
  · intro heq
    by_cases hcase : r ≤ q / (1 + q)
    · rw [min_eq_left hcase] at heq ⊢
      apply le_antisymm hxr
      by_contra hnot
      have hxr' : x < r := lt_of_not_ge hnot
      have hxr1 : 0 < 1 - x := by linarith
      have hrr1 : 0 < 1 - r := by linarith
      have hz : 0 < (1 - x) / (1 - r) := div_pos hxr1 hrr1
      have hz1 : (1 - x) / (1 - r) ≠ 1 := by
        intro h
        rw [div_eq_one_iff_eq (ne_of_gt hrr1)] at h
        linarith
      have hlog := Real.log_lt_sub_one_of_pos hz hz1
      rw [Real.log_div (ne_of_gt hxr1) (ne_of_gt hrr1)] at hlog
      have hcoef : 1 / (1 - r) ≤ 1 + q := by
        rw [le_div_iff₀ hqden] at hcase
        rw [div_le_iff₀ hrr1]
        nlinarith
      have hdiff : 0 < r - x := sub_pos.mpr hxr'
      have hmul : (r - x) / (1 - r) ≤ (1 + q) * (r - x) := by
        simpa [div_eq_mul_inv, mul_comm] using
          (mul_le_mul_of_nonneg_right hcoef (le_of_lt hdiff))
      have hratio :
          (1 - x) / (1 - r) - 1 = (r - x) / (1 - r) := by
        field_simp [ne_of_gt hrr1]
        ring
      have hpos :
          0 < (-q * x - Real.log (1 - x) - x) -
            (-q * r - Real.log (1 - r) - r) := by
        calc
          0 < (r - x) / (1 - r) -
              (Real.log (1 - x) - Real.log (1 - r)) := by
                rw [← hratio]
                linarith
          _ ≤ (1 + q) * (r - x) -
              (Real.log (1 - x) - Real.log (1 - r)) := by linarith
          _ = _ := by ring
      linarith
    · have hcase' : q / (1 + q) ≤ r := le_of_not_ge hcase
      rw [min_eq_right hcase'] at heq ⊢
      let s := q / (1 + q)
      have hs1 : s < 1 := hs01
      have hxs1 : 0 < 1 - x := by linarith
      have hss1 : 0 < 1 - s := by linarith
      have hssne : 1 - s ≠ 0 := ne_of_gt hss1
      by_contra hxs
      have hz : 0 < (1 - x) / (1 - s) := div_pos hxs1 hss1
      have hz1 : (1 - x) / (1 - s) ≠ 1 := by
        intro h
        rw [div_eq_one_iff_eq hssne] at h
        apply hxs
        dsimp [s] at h ⊢
        linarith
      have hlog := Real.log_lt_sub_one_of_pos hz hz1
      rw [Real.log_div (ne_of_gt hxs1) hssne] at hlog
      have hqrel : (1 + q) * (1 - s) = 1 := by
        dsimp [s]
        field_simp
        ring
      have hratio :
          (1 - x) / (1 - s) - 1 = (s - x) / (1 - s) := by
        field_simp [hssne]
        ring
      have hlin :
          (1 + q) * (s - x) = (1 - x) / (1 - s) - 1 := by
        rw [hratio, eq_div_iff hssne]
        nlinarith
      have hpos :
          0 < (-q * x - Real.log (1 - x) - x) -
            (-q * s - Real.log (1 - s) - s) := by
        calc
          _ = (1 + q) * (s - x) -
                (Real.log (1 - x) - Real.log (1 - s)) := by ring
          _ = ((1 - x) / (1 - s) - 1) -
                (Real.log (1 - x) - Real.log (1 - s)) := by rw [hlin]
          _ > 0 := by linarith
      dsimp [s] at hpos
      linarith
  · rintro rfl
    rfl

noncomputable def ftrlBallCandidate {d : ℕ} (η r : ℝ)
    (L : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  let s := min r (η * ‖L‖ / (1 + η * ‖L‖))
  if L = 0 then 0 else (-(s / ‖L‖)) • L

lemma ftrlBallCandidate_norm {d : ℕ} {η r : ℝ}
    (hη : 0 ≤ η) (hr0 : 0 ≤ r) (L : EuclideanSpace ℝ (Fin d)) :
    ‖ftrlBallCandidate η r L‖ =
      min r (η * ‖L‖ / (1 + η * ‖L‖)) := by
  let s := min r (η * ‖L‖ / (1 + η * ‖L‖))
  have hq : 0 ≤ η * ‖L‖ := mul_nonneg hη (norm_nonneg _)
  have hden : 0 < 1 + η * ‖L‖ := by linarith
  have hs0 : 0 ≤ s :=
    le_min hr0 (div_nonneg hq (le_of_lt hden))
  by_cases hL : L = 0
  · subst L
    simp [ftrlBallCandidate, min_eq_right hr0]
  · have hnL : 0 < ‖L‖ := norm_pos_iff.mpr hL
    simp only [ftrlBallCandidate, s, hL, if_false, norm_smul, Real.norm_eq_abs]
    change |-(s / ‖L‖)| * ‖L‖ = s
    rw [abs_neg, abs_of_nonneg (div_nonneg hs0 (le_of_lt hnL))]
    field_simp [ne_of_gt hnL]

private lemma ftrlBallCandidate_inner {d : ℕ} {η r : ℝ}
    (hη : 0 ≤ η) (hr0 : 0 ≤ r) (L : EuclideanSpace ℝ (Fin d)) :
    ⟪ftrlBallCandidate η r L, L⟫ =
      -(min r (η * ‖L‖ / (1 + η * ‖L‖))) * ‖L‖ := by
  let s := min r (η * ‖L‖ / (1 + η * ‖L‖))
  have hq : 0 ≤ η * ‖L‖ := mul_nonneg hη (norm_nonneg _)
  have hden : 0 < 1 + η * ‖L‖ := by linarith
  have hs0 : 0 ≤ s :=
    le_min hr0 (div_nonneg hq (le_of_lt hden))
  by_cases hL : L = 0
  · subst L
    simp [ftrlBallCandidate, s]
  · have hnL : 0 < ‖L‖ := norm_pos_iff.mpr hL
    rw [show ftrlBallCandidate η r L = (-(s / ‖L‖)) • L by
      simp [ftrlBallCandidate, s, hL]]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    change -(s / ‖L‖) * ‖L‖ ^ 2 = -s * ‖L‖
    field_simp [ne_of_gt hnL]

private lemma ftrlBallCandidate_isMinOn {d : ℕ} {η r : ℝ}
    (hη : 0 < η) (hr0 : 0 < r) (hr1 : r < 1)
    (L : EuclideanSpace ℝ (Fin d)) :
    IsMinOn
      (fun b : EuclideanSpace ℝ (Fin d) =>
        η * ⟪b, L⟫ + (-Real.log (1 - ‖b‖) - ‖b‖))
      (Metric.closedBall 0 r ∩ Metric.ball 0 1)
      (ftrlBallCandidate η r L) := by
  have hη' : 0 ≤ η := le_of_lt hη
  have hr0' : 0 ≤ r := le_of_lt hr0
  have hcnorm := ftrlBallCandidate_norm hη' hr0' L
  have hcinner := ftrlBallCandidate_inner hη' hr0' L
  have hq : 0 ≤ η * ‖L‖ := mul_nonneg hη' (norm_nonneg _)
  have hden : 0 < 1 + η * ‖L‖ := by linarith
  have hs0 : 0 ≤ min r (η * ‖L‖ / (1 + η * ‖L‖)) :=
    le_min hr0' (div_nonneg hq (le_of_lt hden))
  have hsle : min r (η * ‖L‖ / (1 + η * ‖L‖)) ≤ r := min_le_left _ _
  have hslt : min r (η * ‖L‖ / (1 + η * ‖L‖)) < 1 := hsle.trans_lt hr1
  intro b hb
  have hbnorm : ‖b‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hb.1
  have hinnerlower : -(‖b‖ * ‖L‖) ≤ ⟪b, L⟫ := by
    have habs := abs_real_inner_le_norm b L
    exact neg_le_of_abs_le habs
  have hscaled :
      -(η * ‖L‖) * ‖b‖ ≤ η * ⟪b, L⟫ := by
    nlinarith
  have hrad := radialObjective_min hq hr0 hr1 (norm_nonneg b) hbnorm
  change η * ⟪ftrlBallCandidate η r L, L⟫ +
      (-Real.log (1 - ‖ftrlBallCandidate η r L‖) -
        ‖ftrlBallCandidate η r L‖) ≤
    η * ⟪b, L⟫ + (-Real.log (1 - ‖b‖) - ‖b‖)
  rw [hcinner, hcnorm]
  nlinarith

private lemma ftrlBallCandidate_mem {d : ℕ} {η r : ℝ}
    (hη : 0 ≤ η) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (L : EuclideanSpace ℝ (Fin d)) :
    ftrlBallCandidate η r L ∈
      Metric.closedBall 0 r ∩ Metric.ball 0 1 := by
  have hnorm := ftrlBallCandidate_norm hη hr0 L
  have hsle :
      min r (η * ‖L‖ / (1 + η * ‖L‖)) ≤ r := min_le_left _ _
  constructor
  · simpa [Metric.mem_closedBall, dist_zero_right, hnorm] using hsle
  · have hslt :
        min r (η * ‖L‖ / (1 + η * ‖L‖)) < 1 := hsle.trans_lt hr1
    simpa [Metric.mem_ball, dist_zero_right, hnorm] using hslt

private lemma ftrlBallCandidate_eq_of_isMinOn {d : ℕ} {η r : ℝ}
    (hη : 0 < η) (hr0 : 0 < r) (hr1 : r < 1)
    (L b : EuclideanSpace ℝ (Fin d))
    (hbmem : b ∈ Metric.closedBall 0 r ∩ Metric.ball 0 1)
    (hbmin : IsMinOn
      (fun z : EuclideanSpace ℝ (Fin d) =>
        η * ⟪z, L⟫ + (-Real.log (1 - ‖z‖) - ‖z‖))
      (Metric.closedBall 0 r ∩ Metric.ball 0 1) b) :
    b = ftrlBallCandidate η r L := by
  let c := ftrlBallCandidate η r L
  let s := min r (η * ‖L‖ / (1 + η * ‖L‖))
  have hη' : 0 ≤ η := le_of_lt hη
  have hr0' : 0 ≤ r := le_of_lt hr0
  have hcnorm : ‖c‖ = s := by
    simpa [c, s] using ftrlBallCandidate_norm hη' hr0' L
  have hcinner : ⟪c, L⟫ = -s * ‖L‖ := by
    simpa [c, s] using ftrlBallCandidate_inner hη' hr0' L
  have hcmem := ftrlBallCandidate_mem hη' hr0' hr1 L
  have hcmin := ftrlBallCandidate_isMinOn hη hr0 hr1 L
  have hbc :
      η * ⟪b, L⟫ + (-Real.log (1 - ‖b‖) - ‖b‖) ≤
        η * ⟪c, L⟫ + (-Real.log (1 - ‖c‖) - ‖c‖) := by
    simpa [c] using hbmin hcmem
  have hcb :
      η * ⟪c, L⟫ + (-Real.log (1 - ‖c‖) - ‖c‖) ≤
        η * ⟪b, L⟫ + (-Real.log (1 - ‖b‖) - ‖b‖) := by
    simpa [c] using hcmin hbmem
  have hobj :
      η * ⟪b, L⟫ + (-Real.log (1 - ‖b‖) - ‖b‖) =
        η * ⟪c, L⟫ + (-Real.log (1 - ‖c‖) - ‖c‖) :=
    le_antisymm hbc hcb
  have hbnorm_le : ‖b‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hbmem.1
  have hq : 0 ≤ η * ‖L‖ := mul_nonneg hη' (norm_nonneg _)
  have hinnerlower : -(‖b‖ * ‖L‖) ≤ ⟪b, L⟫ :=
    neg_le_of_abs_le (abs_real_inner_le_norm b L)
  have hscaled :
      -(η * ‖L‖) * ‖b‖ ≤ η * ⟪b, L⟫ := by
    nlinarith
  have hrad := radialObjective_min hq hr0 hr1 (norm_nonneg b) hbnorm_le
  have hrad_eq :
      -(η * ‖L‖) * ‖b‖ - Real.log (1 - ‖b‖) - ‖b‖ =
        -(η * ‖L‖) * s - Real.log (1 - s) - s := by
    rw [hcinner, hcnorm] at hobj
    dsimp at hrad
    nlinarith
  have hbnorm : ‖b‖ = s := by
    exact (radialObjective_eq_min_iff hq hr0 hr1
      (norm_nonneg b) hbnorm_le).mp (by simpa [s] using hrad_eq)
  have hbinner : ⟪b, L⟫ = -s * ‖L‖ := by
    rw [hbnorm] at hscaled hobj
    rw [hcinner, hcnorm] at hobj
    nlinarith
  by_cases hL : L = 0
  · subst L
    have hb0 : b = 0 := by
      exact norm_eq_zero.mp (by
        simpa [s, min_eq_right hr0'] using hbnorm)
    subst b
    simp [c, ftrlBallCandidate]
  · have hnL : 0 < ‖L‖ := norm_pos_iff.mpr hL
    have hcform : c = (-(s / ‖L‖)) • L := by
      simp [c, ftrlBallCandidate, s, hL]
    have hbcinner : ⟪b, c⟫ = s ^ 2 := by
      rw [hcform, real_inner_smul_right, hbinner]
      field_simp [ne_of_gt hnL]
    have hnormsub : ‖b - c‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hbnorm, hcnorm, hbcinner]
      ring
    have hsub0 : b - c = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖b - c‖]
    exact sub_eq_zero.mp hsub0

lemma ftrlIterates_eq_candidate {d : ℕ} {η r : ℝ}
    (hη : 0 < η) (hr0 : 0 < r) (hr1 : r < 1)
    (Y Abar : ℕ → EuclideanSpace ℝ (Fin d))
    (hiter : IsFTRLIterates η
      (fun b : EuclideanSpace ℝ (Fin d) => -Real.log (1 - ‖b‖) - ‖b‖)
      (Metric.ball 0 1) (Metric.closedBall 0 r) Y Abar) :
    ∀ t, Abar t =
      ftrlBallCandidate η r (∑ s ∈ Finset.range t, Y s) := by
  intro t
  cases t with
  | zero =>
      apply ftrlBallCandidate_eq_of_isMinOn hη hr0 hr1
      · simpa [Set.inter_comm] using hiter.init_mem
      · simpa [Set.inter_comm] using hiter.init_isMinOn
  | succ t =>
      apply ftrlBallCandidate_eq_of_isMinOn hη hr0 hr1
      · simpa [Set.inter_comm, Nat.succ_eq_add_one] using hiter.step_mem t
      · have hmin := hiter.step_isMinOn t
        simpa only [Set.inter_comm, inner_sum,
          Nat.succ_eq_add_one] using hmin

lemma measurable_ftrlBallCandidate {d : ℕ} (η r : ℝ) :
    @Measurable (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d))
      (borel (EuclideanSpace ℝ (Fin d))) (borel (EuclideanSpace ℝ (Fin d)))
      (ftrlBallCandidate (d := d) η r) := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  change Measurable (ftrlBallCandidate (d := d) η r)
  unfold ftrlBallCandidate
  refine Measurable.ite ?_ measurable_const ?_
  · simpa only [Set.setOf_eq_eq_singleton] using
      (measurableSet_singleton
        (0 : EuclideanSpace ℝ (Fin d)))
  · have hf : Measurable (fun L : EuclideanSpace ℝ (Fin d) =>
        -(min r (η * ‖L‖ / (1 + η * ‖L‖)) / ‖L‖)) := by measurability
    exact hf.smul measurable_id

lemma ftrlProcess_measurable
    {d : ℕ} {η r : ℝ} (hη : 0 < η) (hr0 : 0 < r) (hr1 : r < 1)
    {Ω : Type*} [MeasurableSpace Ω]
    (V : ℕ → Ω → ℝ) (W : ℕ → Ω → Fin d × Bool)
    (hVmeas : ∀ t, Measurable (V t)) (hWmeas : ∀ t, Measurable (W t))
    (y : ℕ → EuclideanSpace ℝ (Fin d))
    (Abar A Yhat : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hftrl : ∀ ω, IsFTRLIterates η
      (fun b : EuclideanSpace ℝ (Fin d) => -Real.log (1 - ‖b‖) - ‖b‖)
      (Metric.ball 0 1) (Metric.closedBall 0 r)
      (fun t => Yhat t ω) (fun t => Abar t ω))
    (hA : ∀ t ω, A t ω =
      if V t ω < 1 - ‖Abar t ω‖ then
        (if (W t ω).2 then (1 : ℝ) else -1) •
          EuclideanSpace.single (W t ω).1 1
      else ‖Abar t ω‖⁻¹ • Abar t ω)
    (hY : ∀ t ω, Yhat t ω =
      (if V t ω < 1 - ‖Abar t ω‖ then
        d * ⟪A t ω, y t⟫ / (1 - ‖Abar t ω‖) else 0) • A t ω) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
      borel (EuclideanSpace ℝ (Fin d))
    (∀ t, Measurable (Abar t)) ∧
      (∀ t, Measurable (A t)) ∧ ∀ t, Measurable (Yhat t) := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  have hAbar_eq (t : ℕ) :
      Abar t = fun ω =>
        ftrlBallCandidate η r
          (∑ s ∈ Finset.range t, Yhat s ω) := by
    funext ω
    exact ftrlIterates_eq_candidate hη hr0 hr1
      (fun s => Yhat s ω) (fun s => Abar s ω) (hftrl ω) t
  have hall :
      ∀ t, Measurable (Abar t) ∧
        Measurable (A t) ∧ Measurable (Yhat t) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        have hsum :
            Measurable (fun ω => ∑ s ∈ Finset.range t, Yhat s ω) := by
          classical
          have haux : ∀ u : Finset ℕ, u ⊆ Finset.range t →
              Measurable (fun ω => ∑ s ∈ u, Yhat s ω) := by
            intro u hu
            induction u using Finset.induction_on with
            | empty => simpa using
                (measurable_const :
                  Measurable (fun _ : Ω =>
                    (0 : EuclideanSpace ℝ (Fin d))))
            | @insert a u ha ihu =>
                have hat : a < t :=
                  Finset.mem_range.mp (hu (Finset.mem_insert_self a u))
                have hut : u ⊆ Finset.range t := fun i hi =>
                  hu (Finset.mem_insert_of_mem hi)
                simpa [Finset.sum_insert ha, Pi.add_def] using
                  ((ih a hat).2.2.add (ihu hut))
          exact haux (Finset.range t) (fun _ h => h)
        have hAbarMeas : Measurable (Abar t) := by
          rw [hAbar_eq t]
          exact (measurable_ftrlBallCandidate η r).comp hsum
        have hAeq :
            A t = fun ω =>
              if V t ω < 1 - ‖Abar t ω‖ then
                (if (W t ω).2 then (1 : ℝ) else -1) •
                  EuclideanSpace.single (W t ω).1 1
              else ‖Abar t ω‖⁻¹ • Abar t ω := funext (hA t)
        have hAMeas : Measurable (A t) := by
          rw [hAeq]
          have hevent : MeasurableSet
              {ω | V t ω < 1 - ‖Abar t ω‖} :=
            measurableSet_lt (hVmeas t)
              (measurable_const.sub hAbarMeas.norm)
          have hexplore :
              Measurable (fun ω =>
                (if (W t ω).2 then (1 : ℝ) else -1) •
                  EuclideanSpace.single (W t ω).1 (1 : ℝ)) := by
            simpa [Function.comp_def] using
              (measurable_of_finite (fun u : Fin d × Bool =>
              (if u.2 then (1 : ℝ) else -1) •
                EuclideanSpace.single u.1 (1 : ℝ))).comp (hWmeas t)
          have hexploit :
              Measurable (fun ω =>
                ‖Abar t ω‖⁻¹ • Abar t ω) :=
            hAbarMeas.norm.inv.smul hAbarMeas
          exact Measurable.ite hevent hexplore hexploit
        have hYeq :
            Yhat t = fun ω =>
              (if V t ω < 1 - ‖Abar t ω‖ then
                d * ⟪A t ω, y t⟫ / (1 - ‖Abar t ω‖) else 0) •
                  A t ω := funext (hY t)
        have hYMeas : Measurable (Yhat t) := by
          rw [hYeq]
          have hevent : MeasurableSet
              {ω | V t ω < 1 - ‖Abar t ω‖} :=
            measurableSet_lt (hVmeas t)
              (measurable_const.sub hAbarMeas.norm)
          have htrue :
              Measurable (fun ω =>
                d * ⟪A t ω, y t⟫ /
                  (1 - ‖Abar t ω‖)) := by
            fun_prop
          have hscalar :
              Measurable (fun ω =>
                if V t ω < 1 - ‖Abar t ω‖ then
                  d * ⟪A t ω, y t⟫ /
                    (1 - ‖Abar t ω‖)
                else 0) :=
            Measurable.ite hevent htrue measurable_const
          exact hscalar.smul hAMeas
        exact ⟨hAbarMeas, hAMeas, hYMeas⟩
  exact ⟨fun t => (hall t).1, fun t => (hall t).2.1,
    fun t => (hall t).2.2⟩

end BanditAlgorithm

namespace BanditAlgorithm

private noncomputable def radialPotential (x : ℝ) : ℝ :=
  -Real.log (1 - x) - x

private lemma radialPotential_hasDerivAt_zero :
    HasDerivAt radialPotential 0 0 := by
  unfold radialPotential
  have hin : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 :=
    (hasDerivAt_id' (x := (0 : ℝ))).const_sub 1
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1) 0 := by
    have hl := (Real.hasDerivAt_log (by norm_num : (1 : ℝ) - 0 ≠ 0)).comp 0 hin
    exact hl.congr_deriv (by norm_num)
  exact (hlog.neg.sub (hasDerivAt_id' (x := (0 : ℝ)))).congr_deriv (by norm_num)

private lemma radialPotential_hasDerivAt {x : ℝ} (hx : x < 1) :
    HasDerivAt radialPotential (x / (1 - x)) x := by
  unfold radialPotential
  have hgap : 1 - x ≠ 0 := by linarith
  have hin : HasDerivAt (fun z : ℝ => 1 - z) (-1) x :=
    (hasDerivAt_id' (x := x)).const_sub 1
  have hlog : HasDerivAt (fun z : ℝ => Real.log (1 - z))
      (-(1 - x)⁻¹) x := by
    have hl := (Real.hasDerivAt_log hgap).comp x hin
    exact hl.congr_deriv (by ring)
  refine (hlog.neg.sub (hasDerivAt_id' (x := x))).congr_deriv ?_
  field_simp
  ring

private lemma radialPotential_convexOn :
    ConvexOn ℝ (Set.Ico (0 : ℝ) 1) radialPotential := by
  apply MonotoneOn.convexOn_of_deriv (convex_Ico 0 1)
  · intro x hx
    exact (radialPotential_hasDerivAt hx.2).continuousAt.continuousWithinAt
  · intro x hx
    exact (radialPotential_hasDerivAt (by
      have hmem : x ∈ Set.Ico (0 : ℝ) 1 := interior_subset hx
      exact hmem.2)).differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    have hxm : x ∈ Set.Ico (0 : ℝ) 1 := interior_subset hx
    have hym : y ∈ Set.Ico (0 : ℝ) 1 := interior_subset hy
    rw [(radialPotential_hasDerivAt hxm.2).deriv,
      (radialPotential_hasDerivAt hym.2).deriv]
    rw [div_le_div_iff₀ (by linarith [hxm.2]) (by linarith [hym.2])]
    nlinarith

private lemma radialPotential_monotoneOn :
    MonotoneOn radialPotential (Set.Ico (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
  · intro x hx
    exact (radialPotential_hasDerivAt hx.2).continuousAt.continuousWithinAt
  · intro x hx
    exact (radialPotential_hasDerivAt (by
      have hmem : x ∈ Set.Ico (0 : ℝ) 1 := interior_subset hx
      exact hmem.2)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hmem : x ∈ Set.Ico (0 : ℝ) 1 := interior_subset hx
    rw [(radialPotential_hasDerivAt hmem.2).deriv]
    exact div_nonneg hmem.1 (by linarith [hmem.2])

private lemma ballPotential_convexOn {d : ℕ} :
    ConvexOn ℝ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      (fun b => -Real.log (1 - ‖b‖) - ‖b‖) := by
  have hball : Convex ℝ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    convex_ball 0 1
  refine ⟨hball, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxnorm : ‖x‖ ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · exact norm_nonneg x
    · simpa [Metric.mem_ball, dist_zero_right] using hx
  have hynorm : ‖y‖ ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · exact norm_nonneg y
    · simpa [Metric.mem_ball, dist_zero_right] using hy
  have hmixnorm : ‖a • x + b • y‖ ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · exact norm_nonneg _
    · have hm := hball hx hy ha hb hab
      simpa [Metric.mem_ball, dist_zero_right] using hm
  have hnormle : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc
      _ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = _ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
  have hscalarmem : a * ‖x‖ + b * ‖y‖ ∈ Set.Ico (0 : ℝ) 1 :=
    (convex_Ico (0 : ℝ) 1) hxnorm hynorm ha hb hab
  have hmono := radialPotential_monotoneOn hmixnorm hscalarmem hnormle
  have hconv := radialPotential_convexOn.2 hxnorm hynorm ha hb hab
  simpa [radialPotential, smul_eq_mul] using hmono.trans hconv

private lemma ballPotential_hasFDerivAt_zero {d : ℕ} :
    HasFDerivAt
      (fun b : EuclideanSpace ℝ (Fin d) =>
        -Real.log (1 - ‖b‖) - ‖b‖)
      (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have ho := radialPotential_hasDerivAt_zero.isLittleO
  have hc : Tendsto
      (fun h : EuclideanSpace ℝ (Fin d) => ‖h‖)
      (nhds (0 : EuclideanSpace ℝ (Fin d))) (nhds (0 : ℝ)) :=
    tendsto_norm_zero
  have hcomp := ho.comp_tendsto hc
  have hnorm :
      (fun h : EuclideanSpace ℝ (Fin d) =>
        radialPotential ‖h‖) =o[nhds 0] fun h => h := by
    apply Asymptotics.isLittleO_norm_right.mp
    simpa [Function.comp_def, radialPotential] using hcomp
  simpa [radialPotential] using hnorm

private lemma ballPotential_differentiableAt_zero {d : ℕ} :
    DifferentiableAt ℝ
      (fun b : EuclideanSpace ℝ (Fin d) =>
        -Real.log (1 - ‖b‖) - ‖b‖) 0 :=
  (ballPotential_hasFDerivAt_zero (d := d)).differentiableAt

private lemma ballPotential_differentiableAt {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d)) (hb : ‖b‖ < 1) :
    DifferentiableAt ℝ
      (fun z : EuclideanSpace ℝ (Fin d) =>
        -Real.log (1 - ‖z‖) - ‖z‖) b := by
  by_cases h0 : b = 0
  · simpa [h0] using (ballPotential_differentiableAt_zero (d := d))
  · have hn : DifferentiableAt ℝ
        (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖) b :=
      (differentiableAt_id.norm ℝ h0)
    have hone : 1 - ‖b‖ ≠ 0 := by linarith
    have hin : DifferentiableAt ℝ
        (fun z : EuclideanSpace ℝ (Fin d) => 1 - ‖z‖) b :=
      (differentiableAt_const (c := (1 : ℝ))).sub hn
    exact (((Real.hasDerivAt_log hone).differentiableAt.comp b hin).neg.sub hn)

private lemma log_quadratic_gap {z : ℝ} (hz0 : 0 < z) (hz2 : z ≤ 2) :
    (z - 1) ^ 2 / 4 ≤ z - 1 - Real.log z := by
  let h : ℝ → ℝ := fun x => x - 1 - Real.log x - (x - 1) ^ 2 / 4
  have hder (x : ℝ) (hx : 0 < x) :
      HasDerivAt h ((x - 1) * (2 - x) / (2 * x)) x := by
    dsimp [h]
    have hlog := Real.hasDerivAt_log (ne_of_gt hx)
    have h1 := (((hasDerivAt_id' (x := x)).sub
        (hasDerivAt_const x (1 : ℝ))).sub hlog).sub
        ((((hasDerivAt_id' (x := x)).sub
          (hasDerivAt_const x (1 : ℝ))).pow 2).div_const 4)
    refine h1.congr_deriv ?_
    simp only [Pi.sub_apply]
    field_simp
    ring
  have hcont {a b : ℝ} (ha : 0 < a) : ContinuousOn h (Set.Icc a b) := by
    intro x hx
    exact (hder x (by linarith [hx.1])).continuousAt.continuousWithinAt
  by_cases hz1 : z ≤ 1
  · have hanti : AntitoneOn h (Set.Icc z 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc z 1) (hcont hz0)
      · intro x hx
        exact (hder x (by
          have : x ∈ Set.Icc z 1 := interior_subset hx
          linarith [this.1])).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hder x (by
          have : x ∈ Set.Icc z 1 := interior_subset hx
          linarith [this.1])).deriv]
        have hmem : x ∈ Set.Icc z 1 := interior_subset hx
        have hx0 : 0 < 2 * x := mul_pos two_pos (by linarith [hmem.1])
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith [hmem.2]) (by linarith [hmem.2]))
          (le_of_lt hx0)
    have hle := hanti (show z ∈ Set.Icc z 1 from ⟨le_rfl, hz1⟩)
      (show 1 ∈ Set.Icc z 1 from ⟨hz1, le_rfl⟩) hz1
    dsimp [h] at hle
    norm_num at hle
    linarith
  · have hz1' : 1 ≤ z := le_of_not_ge hz1
    have hmono : MonotoneOn h (Set.Icc 1 z) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 1 z) (hcont one_pos)
      · intro x hx
        exact (hder x (by
          have : x ∈ Set.Icc 1 z := interior_subset hx
          linarith [this.1])).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hder x (by
          have : x ∈ Set.Icc 1 z := interior_subset hx
          linarith [this.1])).deriv]
        have hmem : x ∈ Set.Icc 1 z := interior_subset hx
        have hx0 : 0 < 2 * x := mul_pos two_pos (by linarith [hmem.1])
        have hx1 : 0 ≤ x - 1 := sub_nonneg.mpr hmem.1
        have hx2 : 0 ≤ 2 - x := by linarith [hmem.2, hz2]
        exact div_nonneg (mul_nonneg hx1 hx2)
          (le_of_lt hx0)
    have hle := hmono (show 1 ∈ Set.Icc 1 z from ⟨le_rfl, hz1'⟩)
      (show z ∈ Set.Icc 1 z from ⟨hz1', le_rfl⟩) hz1'
    dsimp [h] at hle
    norm_num at hle
    linarith

private lemma hasGradientAt_norm_ne_zero {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d)) (hb : b ≠ 0) :
    HasGradientAt (fun z : EuclideanSpace ℝ (Fin d) => ‖z‖)
      (‖b‖⁻¹ • b) b := by
  have hsq : ‖b‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hb)
  have hs := (hasStrictFDerivAt_norm_sq b).hasFDerivAt.sqrt hsq
  have hfun : (fun y : EuclideanSpace ℝ (Fin d) => Real.sqrt (‖y‖ ^ 2)) =
      fun z => ‖z‖ := by
    funext z
    rw [Real.sqrt_sq (norm_nonneg z)]
  rw [hfun, Real.sqrt_sq (norm_nonneg b)] at hs
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hs.congr_fderiv ?_
  ext z
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, real_inner_smul_left, smul_eq_mul, two_smul,
    ContinuousLinearMap.add_apply]
  field_simp [norm_ne_zero_iff.mpr hb]
  ring

private lemma ballPotential_hasGradientAt {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d)) (hb : ‖b‖ < 1) :
    HasGradientAt
      (fun z : EuclideanSpace ℝ (Fin d) =>
        -Real.log (1 - ‖z‖) - ‖z‖)
      ((1 - ‖b‖)⁻¹ • b) b := by
  by_cases h0 : b = 0
  · subst b
    have hd := ballPotential_hasFDerivAt_zero (d := d)
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa using hd
  · have hn := hasGradientAt_norm_ne_zero b h0
    have hrho : 0 < ‖b‖ := norm_pos_iff.mpr h0
    have hgap : 1 - ‖b‖ ≠ 0 := by linarith
    have hrad : HasDerivAt radialPotential (‖b‖ / (1 - ‖b‖)) ‖b‖ :=
      radialPotential_hasDerivAt hb
    have hc := hrad.comp_hasFDerivAt b hn.hasFDerivAt
    change HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin d) =>
        -Real.log (1 - ‖z‖) - ‖z‖) _ b at hc
    rw [hasGradientAt_iff_hasFDerivAt]
    refine hc.congr_fderiv ?_
    ext z
    simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.smul_apply,
      real_inner_smul_left, smul_eq_mul]
    field_simp [norm_ne_zero_iff.mpr h0, hgap]

private lemma ballPotential_bregman_lower {d : ℕ}
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ < 1) (hy : ‖y‖ < 1)
    (hratio : 1 - ‖y‖ ≤ 2 * (1 - ‖x‖)) :
    ‖y - x‖ ^ 2 / (4 * (1 - ‖x‖)) ≤
      bregmanDiv
        (fun z : EuclideanSpace ℝ (Fin d) =>
          -Real.log (1 - ‖z‖) - ‖z‖) y x := by
  have hpx : 0 < 1 - ‖x‖ := by linarith
  have hpy : 0 < 1 - ‖y‖ := by linarith
  have hpxne : 1 - ‖x‖ ≠ 0 := ne_of_gt hpx
  let z := (1 - ‖y‖) / (1 - ‖x‖)
  have hz0 : 0 < z := div_pos hpy hpx
  have hz2 : z ≤ 2 := by
    dsimp [z]
    exact (div_le_iff₀ hpx).2 hratio
  have hquad := log_quadratic_gap hz0 hz2
  have hlog : Real.log z = Real.log (1 - ‖y‖) - Real.log (1 - ‖x‖) := by
    dsimp [z]
    rw [Real.log_div (ne_of_gt hpy) hpxne]
  have hzsub : z - 1 = (‖x‖ - ‖y‖) / (1 - ‖x‖) := by
    dsimp [z]
    field_simp [hpxne]
    ring
  have hradial_eq :
      (-Real.log (1 - ‖y‖) - ‖y‖) -
          (-Real.log (1 - ‖x‖) - ‖x‖) -
          (‖x‖ / (1 - ‖x‖)) * (‖y‖ - ‖x‖) =
        z - 1 - Real.log z := by
    rw [hlog, hzsub]
    field_simp [hpxne]
    ring
  have hpxle : 1 - ‖x‖ ≤ 1 := by linarith [norm_nonneg x]
  have hradial :
      (‖y‖ - ‖x‖) ^ 2 / (4 * (1 - ‖x‖)) ≤
        (-Real.log (1 - ‖y‖) - ‖y‖) -
          (-Real.log (1 - ‖x‖) - ‖x‖) -
          (‖x‖ / (1 - ‖x‖)) * (‖y‖ - ‖x‖) := by
    rw [hradial_eq]
    have hsquare :
        (‖y‖ - ‖x‖) ^ 2 / (4 * (1 - ‖x‖)) =
          (1 - ‖x‖) * (z - 1) ^ 2 / 4 := by
      rw [hzsub]
      field_simp [hpxne]
      ring
    rw [hsquare]
    have hsq0 : 0 ≤ (z - 1) ^ 2 / 4 := by positivity
    have hscale :
        (1 - ‖x‖) * ((z - 1) ^ 2 / 4) ≤ (z - 1) ^ 2 / 4 :=
      mul_le_of_le_one_left hsq0 hpxle
    linarith
  have hang : 0 ≤ ‖x‖ * ‖y‖ - ⟪x, y⟫ := by
    linarith [real_inner_le_norm x y]
  have hgrad := (ballPotential_hasGradientAt x hx).gradient
  rw [bregmanDiv, hgrad, real_inner_smul_left]
  have hnorm :
      ‖y - x‖ ^ 2 =
        (‖y‖ - ‖x‖) ^ 2 + 2 * (‖x‖ * ‖y‖ - ⟪x, y⟫) := by
    rw [norm_sub_sq_real]
    rw [real_inner_comm y x]
    ring
  rw [hnorm]
  have hangbound :
      2 * (‖x‖ * ‖y‖ - ⟪x, y⟫) / (4 * (1 - ‖x‖)) ≤
        (‖x‖ * ‖y‖ - ⟪x, y⟫) / (1 - ‖x‖) := by
    have hp4 : 0 < 4 * (1 - ‖x‖) := by positivity
    have hp : 0 < 1 - ‖x‖ := hpx
    rw [div_le_iff₀ hp4, div_eq_mul_inv, mul_assoc]
    field_simp [hpxne]
    nlinarith
  have hdecomp :
      ⟪x, y - x⟫ = ⟪x, y⟫ - ‖x‖ ^ 2 := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [hdecomp]
  have hsumdiv :
      ((‖y‖ - ‖x‖) ^ 2 + 2 * (‖x‖ * ‖y‖ - ⟪x, y⟫)) /
          (4 * (1 - ‖x‖)) =
        (‖y‖ - ‖x‖) ^ 2 / (4 * (1 - ‖x‖)) +
          2 * (‖x‖ * ‖y‖ - ⟪x, y⟫) / (4 * (1 - ‖x‖)) := by ring
  rw [hsumdiv]
  calc
    _ ≤ ((-Real.log (1 - ‖y‖) - ‖y‖) -
          (-Real.log (1 - ‖x‖) - ‖x‖) -
          (‖x‖ / (1 - ‖x‖)) * (‖y‖ - ‖x‖)) +
        (‖x‖ * ‖y‖ - ⟪x, y⟫) / (1 - ‖x‖) :=
      add_le_add hradial hangbound
    _ = _ := by
      field_simp [hpxne]
      ring

private lemma one_sub_min_ratio_stable
    {q q' r : ℝ} (hq : 0 ≤ q) (hq' : 0 ≤ q') (hr : r < 1)
    (hclose : |q' - q| ≤ 1 / 2) :
    1 - min r (q' / (1 + q')) ≤
      2 * (1 - min r (q / (1 + q))) := by
  have hden : 0 < 1 + q := by linarith
  have hden' : 0 < 1 + q' := by linarith
  have hqfrac : q / (1 + q) < 1 := by
    rw [div_lt_one hden]
    linarith
  have hqfrac' : q' / (1 + q') < 1 := by
    rw [div_lt_one hden']
    linarith
  have hq'lower : q - 1 / 2 ≤ q' := by
    rw [abs_le] at hclose
    linarith [hclose.1]
  by_cases hnew : r ≤ q' / (1 + q')
  · rw [min_eq_left hnew]
    have hbase : min r (q / (1 + q)) ≤ r := min_le_left _ _
    linarith
  · rw [min_eq_right (le_of_not_ge hnew)]
    by_cases hold : r ≤ q / (1 + q)
    · rw [min_eq_left hold]
      have hrecip : 1 / (1 + q') ≤ 2 * (1 - r) := by
        have hrq : r * (1 + q) ≤ q := (le_div_iff₀ hden).mp hold
        rw [div_le_iff₀ hden']
        nlinarith [mul_nonneg (sub_nonneg.mpr hq'lower) (show 0 ≤ 1 + q by linarith)]
      have hgap' : 1 - q' / (1 + q') = 1 / (1 + q') := by
        field_simp [ne_of_gt hden']
        ring
      rw [hgap']
      exact hrecip
    · rw [min_eq_right (le_of_not_ge hold)]
      have hgap : 1 - q / (1 + q) = 1 / (1 + q) := by
        field_simp [ne_of_gt hden]
        ring
      have hgap' : 1 - q' / (1 + q') = 1 / (1 + q') := by
        field_simp [ne_of_gt hden']
        ring
      rw [hgap, hgap']
      rw [show 2 * (1 / (1 + q)) = 2 / (1 + q) by ring]
      rw [div_le_div_iff₀ hden' hden]
      nlinarith

private lemma ftrlCandidate_gap_stable {d : ℕ}
    {η r : ℝ} (hη : 0 ≤ η) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (L Y : EuclideanSpace ℝ (Fin d)) (hY : η * ‖Y‖ ≤ 1 / 2) :
    1 - ‖ftrlBallCandidate η r (L + Y)‖ ≤
      2 * (1 - ‖ftrlBallCandidate η r L‖) := by
  rw [ftrlBallCandidate_norm hη hr0, ftrlBallCandidate_norm hη hr0]
  apply one_sub_min_ratio_stable
  · positivity
  · positivity
  · exact hr1
  · have hnorm : |‖L + Y‖ - ‖L‖| ≤ ‖Y‖ := by
      simpa using abs_norm_sub_norm_le (L + Y) L
    rw [← mul_sub, abs_mul]
    have hηabs : |η| = η := abs_of_nonneg hη
    rw [hηabs]
    exact (mul_le_mul_of_nonneg_left hnorm hη).trans hY

private lemma signedSingle_norm {d : ℕ} (u : Fin d × Bool) :
    ‖(if u.2 then (1 : ℝ) else -1) •
        EuclideanSpace.single u.1 (1 : ℝ)‖ = 1 := by
  cases u with
  | mk i s =>
      cases s <;> simp [EuclideanSpace.norm_single]

private lemma estimator_small {d : ℕ} (hd : 0 < d)
    {η r : ℝ} (hη : 0 < η) (hr : r = 1 - 2 * η * d)
    {b a yhat y : EuclideanSpace ℝ (Fin d)} {v : ℝ} {w : Fin d × Bool}
    (hbnorm : ‖b‖ ≤ r) (hy : ‖y‖ ≤ 1)
    (ha : a = if v < 1 - ‖b‖ then
        (if w.2 then (1 : ℝ) else -1) • EuclideanSpace.single w.1 1
      else ‖b‖⁻¹ • b)
    (hyhat : yhat =
      (if v < 1 - ‖b‖ then
        d * ⟪a, y⟫ / (1 - ‖b‖) else 0) • a) :
    η * ‖yhat‖ ≤ 1 / 2 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hgap : 2 * η * d ≤ 1 - ‖b‖ := by linarith
  have hgap0 : 0 < 1 - ‖b‖ := lt_of_lt_of_le (by positivity) hgap
  by_cases he : v < 1 - ‖b‖
  · have hanorm : ‖a‖ = 1 := by
      rw [ha, if_pos he]
      exact signedSingle_norm w
    have hinner : |⟪a, y⟫| ≤ 1 := by
      calc
        |⟪a, y⟫| ≤ ‖a‖ * ‖y‖ := abs_real_inner_le_norm a y
        _ ≤ 1 := by rw [hanorm]; simpa using hy
    rw [hyhat, if_pos he, norm_smul, hanorm, mul_one, Real.norm_eq_abs,
      abs_div, abs_mul, abs_of_nonneg (show 0 ≤ (d : ℝ) by positivity),
      abs_of_pos hgap0]
    have hnum : η * ((d : ℝ) * |⟪a, y⟫|) ≤ η * d := by
      exact mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul_of_nonneg_left hinner (le_of_lt hdR)) (le_of_lt hη)
    rw [← mul_div_assoc, div_le_iff₀ hgap0]
    nlinarith
  · rw [hyhat, if_neg he, zero_smul, norm_zero, mul_zero]
    norm_num

private lemma ftrl_pathwise_regret_bound {d n : ℕ} (hd : 0 < d)
    {η r : ℝ} (hη : 0 < η) (hr : r = 1 - 2 * η * d) (hr0 : 0 < r)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (hy : ∀ t, ‖y t‖ ≤ 1)
    (V : ℕ → ℝ) (W : ℕ → Fin d × Bool)
    (Abar A Yhat : ℕ → EuclideanSpace ℝ (Fin d))
    (hftrl : IsFTRLIterates η
      (fun b : EuclideanSpace ℝ (Fin d) => -Real.log (1 - ‖b‖) - ‖b‖)
      (Metric.ball 0 1) (Metric.closedBall 0 r) Yhat Abar)
    (hA : ∀ t, A t =
      if V t < 1 - ‖Abar t‖ then
        (if (W t).2 then (1 : ℝ) else -1) • EuclideanSpace.single (W t).1 1
      else ‖Abar t‖⁻¹ • Abar t)
    (hY : ∀ t, Yhat t =
      (if V t < 1 - ‖Abar t‖ then
        d * ⟪A t, y t⟫ / (1 - ‖Abar t‖) else 0) • A t) :
    ∀ a₀ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      oloRegret Abar Yhat n (r • a₀) ≤
        Real.log (1 / (1 - r)) / η +
          η * ∑ t ∈ Finset.range n, (1 - ‖Abar t‖) * ‖Yhat t‖ ^ 2 := by
  have hr1 : r < 1 := by
    rw [hr]
    have : 0 < 2 * η * (d : ℝ) := by positivity
    linarith
  have hηnonneg : 0 ≤ η := le_of_lt hη
  have hrnonneg : 0 ≤ r := le_of_lt hr0
  have hmem (t : ℕ) : Abar t ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) r ∩ Metric.ball 0 1 := by
    cases t with
    | zero => exact hftrl.init_mem
    | succ t => simpa [Nat.succ_eq_add_one] using hftrl.step_mem t
  have hnormle (t : ℕ) : ‖Abar t‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_zero_right] using (hmem t).1
  have hnormlt (t : ℕ) : ‖Abar t‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using (hmem t).2
  have hsmall (t : ℕ) : η * ‖Yhat t‖ ≤ 1 / 2 :=
    estimator_small hd hη hr (hnormle t) (hy t) (hA t) (hY t)
  have hratio (t : ℕ) :
      1 - ‖Abar (t + 1)‖ ≤ 2 * (1 - ‖Abar t‖) := by
    rw [ftrlIterates_eq_candidate hη hr0 hr1 Yhat Abar hftrl t,
      ftrlIterates_eq_candidate hη hr0 hr1 Yhat Abar hftrl (t + 1),
      Finset.sum_range_succ]
    exact ftrlCandidate_gap_stable hηnonneg hrnonneg hr1 _ _ (hsmall t)
  have hstep (t : ℕ) :
      ⟪Abar t - Abar (t + 1), Yhat t⟫ -
          (1 / η) * bregmanDiv
            (fun b : EuclideanSpace ℝ (Fin d) =>
              -Real.log (1 - ‖b‖) - ‖b‖)
            (Abar (t + 1)) (Abar t) ≤
        η * (1 - ‖Abar t‖) * ‖Yhat t‖ ^ 2 := by
    have hp : 0 < 1 - ‖Abar t‖ := by linarith [hnormlt t]
    have hD := ballPotential_bregman_lower (Abar t) (Abar (t + 1))
      (hnormlt t) (hnormlt (t + 1)) (hratio t)
    have hinner :
        ⟪Abar t - Abar (t + 1), Yhat t⟫ ≤
          ‖Abar t - Abar (t + 1)‖ * ‖Yhat t‖ :=
      real_inner_le_norm _ _
    have hηinv : 0 < 1 / η := by positivity
    have hDscaled :
        (1 / η) * (‖Abar (t + 1) - Abar t‖ ^ 2 /
          (4 * (1 - ‖Abar t‖))) ≤
          (1 / η) * bregmanDiv
            (fun b : EuclideanSpace ℝ (Fin d) =>
              -Real.log (1 - ‖b‖) - ‖b‖)
            (Abar (t + 1)) (Abar t) :=
      mul_le_mul_of_nonneg_left hD (le_of_lt hηinv)
    have hnormsym :
        ‖Abar (t + 1) - Abar t‖ = ‖Abar t - Abar (t + 1)‖ :=
      norm_sub_rev _ _
    rw [hnormsym] at hDscaled
    have hsquare :
        0 ≤ (‖Abar t - Abar (t + 1)‖ -
          2 * η * (1 - ‖Abar t‖) * ‖Yhat t‖) ^ 2 := sq_nonneg _
    have hquad :
        ‖Abar t - Abar (t + 1)‖ * ‖Yhat t‖ -
            (1 / η) * (‖Abar t - Abar (t + 1)‖ ^ 2 /
              (4 * (1 - ‖Abar t‖))) ≤
          η * (1 - ‖Abar t‖) * ‖Yhat t‖ ^ 2 := by
      field_simp [ne_of_gt hη, ne_of_gt hp] at hsquare ⊢
      nlinarith
    linarith
  intro a₀ ha₀
  have ha₀norm : ‖a₀‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using ha₀
  have hranorm : ‖r • a₀‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hrnonneg]
    nlinarith
  have hcompmem : r • a₀ ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) r ∩ Metric.ball 0 1 := by
    constructor
    · simpa [Metric.mem_closedBall, dist_zero_right] using hranorm
    · have : ‖r • a₀‖ < 1 := hranorm.trans_lt hr1
      simpa [Metric.mem_ball, dist_zero_right] using this
  have hne : (Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin d)) r).Nonempty :=
    ⟨0, by simpa [Metric.mem_closedBall] using hrnonneg⟩
  have hbase := BanditAlgorithm.ftrl_regret_bound hη
    (ballPotential_convexOn (d := d)) (convex_closedBall 0 r) hne
    Yhat Abar n hftrl (fun t => ballPotential_differentiableAt _ (hnormlt t))
    (r • a₀) hcompmem
  have hzero : Abar 0 = 0 := by
    rw [ftrlIterates_eq_candidate hη hr0 hr1 Yhat Abar hftrl 0]
    simp [ftrlBallCandidate]
  have hpot :
      ((-Real.log (1 - ‖r • a₀‖) - ‖r • a₀‖) -
          (-Real.log (1 - ‖Abar 0‖) - ‖Abar 0‖)) / η ≤
        Real.log (1 / (1 - r)) / η := by
    simp only [hzero, norm_zero, sub_zero, Real.log_one, neg_zero]
    have hgap0 : 0 < 1 - r := by linarith
    have hgapcomp : 0 < 1 - ‖r • a₀‖ := by linarith [hranorm]
    have hlogmono : Real.log (1 - r) ≤ Real.log (1 - ‖r • a₀‖) :=
      Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hgap0)
        (Set.mem_Ioi.mpr hgapcomp) (by linarith [hranorm])
    have hlog_inv : Real.log (1 / (1 - r)) = -Real.log (1 - r) := by
      rw [one_div, Real.log_inv]
    rw [hlog_inv]
    apply (div_le_div_iff_of_pos_right hη).2
    nlinarith [norm_nonneg (r • a₀)]
  calc
    oloRegret Abar Yhat n (r • a₀) ≤
        ((-Real.log (1 - ‖r • a₀‖) - ‖r • a₀‖) -
          (-Real.log (1 - ‖Abar 0‖) - ‖Abar 0‖)) / η +
          ∑ t ∈ Finset.range n,
            (⟪Abar t - Abar (t + 1), Yhat t⟫ -
              (1 / η) * bregmanDiv
                (fun b : EuclideanSpace ℝ (Fin d) =>
                  -Real.log (1 - ‖b‖) - ‖b‖)
                (Abar (t + 1)) (Abar t)) := hbase
    _ ≤ Real.log (1 / (1 - r)) / η +
          ∑ t ∈ Finset.range n,
            η * (1 - ‖Abar t‖) * ‖Yhat t‖ ^ 2 := by
      gcongr with t ht
      exact hstep t
    _ = Real.log (1 / (1 - r)) / η +
          η * ∑ t ∈ Finset.range n,
            (1 - ‖Abar t‖) * ‖Yhat t‖ ^ 2 := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring

private noncomputable def signedDir {d : ℕ} (u : Fin d × Bool) :
    EuclideanSpace ℝ (Fin d) :=
  (if u.2 then (1 : ℝ) else -1) • EuclideanSpace.single u.1 1

private lemma sum_signedDir {d : ℕ} :
    ∑ u : Fin d × Bool, signedDir u =
      (0 : EuclideanSpace ℝ (Fin d)) := by
  classical
  ext j
  rw [Fintype.sum_prod_type]
  simp [signedDir]

private lemma sum_signedDir_inner_smul {d : ℕ}
    (y : EuclideanSpace ℝ (Fin d)) :
    ∑ u : Fin d × Bool, ⟪signedDir u, y⟫ • signedDir u =
      2 • y := by
  classical
  ext j
  rw [Fintype.sum_prod_type]
  simp [signedDir, real_inner_smul_left, EuclideanSpace.inner_single_left]
  rw [Finset.sum_add_distrib]
  have hs : ∑ i : Fin d,
      y.ofLp i * (@Pi.single (Fin d) (fun _ => ℝ) _ _ i 1 j) = y.ofLp j := by
    calc
      _ = y.ofLp j * (@Pi.single (Fin d) (fun _ => ℝ) _ _ j 1 j) := by
        apply Fintype.sum_eq_single j
        intro i hij
        simp [Pi.single_apply, hij]
      _ = y.ofLp j := by simp
  rw [hs]
  ring

private lemma sum_signedDir_inner_sq {d : ℕ}
    (y : EuclideanSpace ℝ (Fin d)) :
    ∑ u : Fin d × Bool, ⟪signedDir u, y⟫ ^ 2 =
      2 * ‖y‖ ^ 2 := by
  classical
  rw [Fintype.sum_prod_type]
  simp [signedDir, real_inner_smul_left, EuclideanSpace.inner_single_left,
    EuclideanSpace.norm_sq_eq]
  rw [Finset.sum_add_distrib]
  ring

private lemma map_uniform_signed {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : Ω → Fin d × Bool) (hWmeas : Measurable W)
    (hW : ∀ u : Fin d × Bool,
      P {ω | W ω = u} = ((2 * d : ℕ) : ENNReal)⁻¹) :
    Measure.map W P = ((2 * d : ℕ) : ENNReal)⁻¹ • Measure.count := by
  apply Measure.ext_of_singleton
  intro u
  rw [Measure.map_apply hWmeas (measurableSet_singleton u)]
  rw [show W ⁻¹' {u} = {ω | W ω = u} by ext ω; simp]
  rw [hW u, Measure.smul_apply]
  simp

private lemma integral_uniform_signed {d : ℕ} (hd : 0 < d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Fin d × Bool → E) :
    ∫ u, f u ∂(((2 * d : ℕ) : ENNReal)⁻¹ • Measure.count) =
      (1 / (2 * d : ℝ)) • ∑ u, f u := by
  rw [integral_smul_measure, integral_count]
  congr 1
  rw [ENNReal.toReal_inv]
  simp [one_div]

private lemma volume_restrict_Icc_Iio {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ((volume : Measure ℝ).restrict (Set.Icc 0 1)) (Set.Iio p) = ENNReal.ofReal p := by
  rw [Measure.restrict_apply measurableSet_Iio]
  have hset : Set.Icc (0 : ℝ) 1 ∩ Set.Iio p = Set.Ico 0 p := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
    constructor
    · rintro ⟨⟨hx0, hx1⟩, hxp⟩
      exact ⟨hx0, hxp⟩
    · rintro ⟨hx0, hxp⟩
      exact ⟨⟨hx0, hxp.le.trans hp1⟩, hxp⟩
  rw [Set.inter_comm, hset, Real.volume_Ico]
  simp [hp0]

private lemma integral_uniform_Icc_indicator_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (c : E) :
    ∫ v, (if v < p then c else 0)
        ∂((volume : Measure ℝ).restrict (Set.Icc 0 1)) = p • c := by
  have hmeas : MeasurableSet (Set.Iio p) := measurableSet_Iio
  have heq : (fun v : ℝ => if v < p then c else 0) =
      Set.indicator (Set.Iio p) (fun _ => c) := by
    funext v
    simp [Set.indicator, Set.mem_Iio]
  rw [heq, integral_indicator_const c hmeas]
  change (((volume : Measure ℝ).restrict (Set.Icc 0 1)) (Set.Iio p)).toReal • c = p • c
  rw [volume_restrict_Icc_Iio hp0 hp1, ENNReal.toReal_ofReal hp0]

private lemma integral_uniform_Icc_ite_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (c e : E) :
    ∫ v, (if v < p then c else e)
        ∂((volume : Measure ℝ).restrict (Set.Icc 0 1)) =
      p • c + (1 - p) • e := by
  let μ := (volume : Measure ℝ).restrict (Set.Icc 0 1)
  have hdecomp : (fun v : ℝ => if v < p then c else e) =
      fun v => (if v < p then c - e else 0) + e := by
    funext v
    split_ifs <;> simp_all
  rw [hdecomp]
  have hmeas : StronglyMeasurable (fun v : ℝ => if v < p then c - e else 0) :=
    StronglyMeasurable.ite (p := fun v => v < p) measurableSet_Iio
      stronglyMeasurable_const stronglyMeasurable_const
  have h1 : Integrable (fun v : ℝ => if v < p then c - e else 0) μ :=
    Integrable.of_bound hmeas.aestronglyMeasurable ‖c - e‖
      (Eventually.of_forall fun v => by
        by_cases hv : v < p
        · simp [hv]
        · simp [hv, norm_nonneg])
  have h2 : Integrable (fun _ : ℝ => e) μ := integrable_const e
  rw [integral_add h1 h2, integral_uniform_Icc_indicator_const p hp0 hp1,
    integral_const]
  have hμ : μ.real Set.univ = 1 := by
    change (((volume : Measure ℝ).restrict (Set.Icc 0 1)) Set.univ).toReal = 1
    rw [Measure.restrict_apply MeasurableSet.univ]
    simp [Real.volume_Icc]
  rw [hμ, one_smul]
  module

private noncomputable def purePlay {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d)) (v : ℝ) (u : Fin d × Bool) :
    EuclideanSpace ℝ (Fin d) :=
  if v < 1 - ‖b‖ then signedDir u else ‖b‖⁻¹ • b

private noncomputable def pureEstimator {d : ℕ}
    (y b : EuclideanSpace ℝ (Fin d)) (v : ℝ) (u : Fin d × Bool) :
    EuclideanSpace ℝ (Fin d) :=
  (if v < 1 - ‖b‖ then
    d * ⟪purePlay b v u, y⟫ / (1 - ‖b‖) else 0) • purePlay b v u

private lemma iterated_integral_purePlay {d : ℕ} (hd : 0 < d)
    (b : EuclideanSpace ℝ (Fin d)) (hb : ‖b‖ < 1) :
    ∫ u, ∫ v, purePlay b v u
        ∂((volume : Measure ℝ).restrict (Set.Icc 0 1))
      ∂(((2 * d : ℕ) : ENNReal)⁻¹ • Measure.count) = b := by
  have hp0 : 0 ≤ 1 - ‖b‖ := by linarith
  have hp1 : 1 - ‖b‖ ≤ 1 := by linarith [norm_nonneg b]
  simp_rw [purePlay]
  rw [show (fun u : Fin d × Bool =>
      ∫ v, (if v < 1 - ‖b‖ then signedDir u else ‖b‖⁻¹ • b)
        ∂((volume : Measure ℝ).restrict (Set.Icc 0 1))) =
      fun u => (1 - ‖b‖) • signedDir u + ‖b‖ • (‖b‖⁻¹ • b) by
        funext u
        simpa using integral_uniform_Icc_ite_const (1 - ‖b‖) hp0 hp1
          (signedDir u) (‖b‖⁻¹ • b)]
  rw [integral_uniform_signed hd]
  rw [Finset.sum_add_distrib]
  rw [← Finset.smul_sum, sum_signedDir, smul_zero, zero_add]
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool]
  by_cases h0 : b = 0
  · simp [h0]
  · have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr h0
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
    rw [← Nat.cast_smul_eq_nsmul ℝ]
    simp only [Nat.cast_mul, Nat.cast_ofNat, smul_smul]
    field_simp [hn, hdR]
    simp

private lemma iterated_integral_pureEstimator {d : ℕ} (hd : 0 < d)
    (y b : EuclideanSpace ℝ (Fin d)) (hb : ‖b‖ < 1) :
    ∫ u, ∫ v, pureEstimator y b v u
        ∂((volume : Measure ℝ).restrict (Set.Icc 0 1))
      ∂(((2 * d : ℕ) : ENNReal)⁻¹ • Measure.count) = y := by
  have hp0 : 0 ≤ 1 - ‖b‖ := by linarith
  have hp1 : 1 - ‖b‖ ≤ 1 := by linarith [norm_nonneg b]
  have hpne : 1 - ‖b‖ ≠ 0 := by linarith
  have hinner (u : Fin d × Bool) :
      ∫ v, pureEstimator y b v u
          ∂((volume : Measure ℝ).restrict (Set.Icc 0 1)) =
        (d : ℝ) • (⟪signedDir u, y⟫ • signedDir u) := by
    unfold pureEstimator purePlay
    rw [show (fun v : ℝ =>
        (if v < 1 - ‖b‖ then
          ↑d * ⟪if v < 1 - ‖b‖ then signedDir u else ‖b‖⁻¹ • b, y⟫ /
            (1 - ‖b‖)
          else 0) •
          (if v < 1 - ‖b‖ then signedDir u else ‖b‖⁻¹ • b)) =
        fun v => if v < 1 - ‖b‖ then
          (↑d * ⟪signedDir u, y⟫ / (1 - ‖b‖)) • signedDir u else 0 by
          funext v
          split_ifs <;> simp_all]
    rw [integral_uniform_Icc_indicator_const (1 - ‖b‖) hp0 hp1]
    rw [smul_smul]
    field_simp [hpne]
    rw [smul_smul]
  simp_rw [hinner]
  rw [integral_uniform_signed hd, ← Finset.smul_sum, sum_signedDir_inner_smul]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  simp only [smul_smul, Nat.cast_ofNat]
  field_simp [hdR]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  norm_num [smul_smul]

private lemma iterated_integral_pureEstimator_sq {d : ℕ} (hd : 0 < d)
    (y b : EuclideanSpace ℝ (Fin d)) (hb : ‖b‖ < 1) :
    ∫ u, ∫ v, (1 - ‖b‖) * ‖pureEstimator y b v u‖ ^ 2
        ∂((volume : Measure ℝ).restrict (Set.Icc 0 1))
      ∂(((2 * d : ℕ) : ENNReal)⁻¹ • Measure.count) =
        d * ‖y‖ ^ 2 := by
  have hp0 : 0 ≤ 1 - ‖b‖ := by linarith
  have hp1 : 1 - ‖b‖ ≤ 1 := by linarith [norm_nonneg b]
  have hpne : 1 - ‖b‖ ≠ 0 := by linarith
  have hinner (u : Fin d × Bool) :
      ∫ v, (1 - ‖b‖) * ‖pureEstimator y b v u‖ ^ 2
          ∂((volume : Measure ℝ).restrict (Set.Icc 0 1)) =
        (d : ℝ) ^ 2 * ⟪signedDir u, y⟫ ^ 2 := by
    unfold pureEstimator purePlay
    rw [show (fun v : ℝ =>
        (1 - ‖b‖) *
          ‖(if v < 1 - ‖b‖ then
              ↑d * ⟪if v < 1 - ‖b‖ then signedDir u else ‖b‖⁻¹ • b, y⟫ /
                (1 - ‖b‖)
            else 0) •
            (if v < 1 - ‖b‖ then signedDir u else ‖b‖⁻¹ • b)‖ ^ 2) =
        fun v => if v < 1 - ‖b‖ then
          (1 - ‖b‖) *
            (↑d * ⟪signedDir u, y⟫ / (1 - ‖b‖)) ^ 2 else 0 by
          funext v
          split_ifs with h
          · rw [norm_smul]
            have hu : ‖signedDir u‖ = 1 := by
              exact signedSingle_norm u
            rw [hu, mul_one, Real.norm_eq_abs, sq_abs]
          · simp]
    rw [integral_uniform_Icc_indicator_const (1 - ‖b‖) hp0 hp1]
    simp only [smul_eq_mul]
    field_simp [hpne]
  simp_rw [hinner]
  rw [integral_uniform_signed hd, ← Finset.mul_sum, sum_signedDir_inner_sq]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  simp only [smul_eq_mul]
  field_simp [hdR]

private abbrev FTRLSeed (d : ℕ) := ℝ × (Fin d × Bool)

/-- The cumulative estimated loss obtained by replaying a finite prefix of seeds. -/
private noncomputable def pureCumLoss {d : ℕ} (η r : ℝ)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) :
    ∀ t, (Fin t → FTRLSeed d) → EuclideanSpace ℝ (Fin d)
  | 0, _ => 0
  | t + 1, ξ =>
      let L := pureCumLoss η r y t (fun i => ξ i.castSucc)
      let b := ftrlBallCandidate η r L
      let z := ξ (Fin.last t)
      L + pureEstimator (y t) b z.1 z.2

private noncomputable def pureState {d : ℕ} (η r : ℝ)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ)
    (ξ : Fin t → FTRLSeed d) : EuclideanSpace ℝ (Fin d) :=
  ftrlBallCandidate η r (pureCumLoss η r y t ξ)

private lemma measurable_pureEstimator_seed {d : ℕ}
    (y : EuclideanSpace ℝ (Fin d)) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
      borel (EuclideanSpace ℝ (Fin d))
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d =>
      pureEstimator y z.1 z.2.1 z.2.2) := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  have hevent : MeasurableSet
      {z : EuclideanSpace ℝ (Fin d) × FTRLSeed d |
        z.2.1 < 1 - ‖z.1‖} :=
    measurableSet_lt measurable_snd.fst
      (measurable_const.sub measurable_fst.norm)
  have hsigned : Measurable
      (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d => signedDir z.2.2) :=
    (measurable_of_finite signedDir).comp measurable_snd.snd
  have hcoef : Measurable
      (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d =>
        (d : ℝ) * ⟪signedDir z.2.2, y⟫ / (1 - ‖z.1‖)) :=
    (measurable_const.mul hsigned.inner_const).div
      (measurable_const.sub measurable_fst.norm)
  have hexplore : Measurable
      (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d =>
        ((d : ℝ) * ⟪signedDir z.2.2, y⟫ / (1 - ‖z.1‖)) • signedDir z.2.2) :=
    hcoef.smul hsigned
  rw [show (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d =>
      pureEstimator y z.1 z.2.1 z.2.2) =
      fun z => if z.2.1 < 1 - ‖z.1‖ then
        ((d : ℝ) * ⟪signedDir z.2.2, y⟫ / (1 - ‖z.1‖)) • signedDir z.2.2
      else 0 by
    funext z
    unfold pureEstimator purePlay
    split_ifs <;> simp_all]
  exact Measurable.ite hevent hexplore measurable_const

private lemma measurable_pureCumLoss {d : ℕ} (η r : ℝ)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
      borel (EuclideanSpace ℝ (Fin d))
    Measurable (pureCumLoss η r y t) := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  induction t with
  | zero => simpa [pureCumLoss] using
      (measurable_const : Measurable (fun _ : Fin 0 → FTRLSeed d =>
        (0 : EuclideanSpace ℝ (Fin d))))
  | succ t ih =>
      simp only [pureCumLoss]
      have hrestr : Measurable (fun ξ : Fin (t + 1) → FTRLSeed d =>
          fun i : Fin t => ξ i.castSucc) := by
        fun_prop
      have hL : Measurable (fun ξ : Fin (t + 1) → FTRLSeed d =>
          pureCumLoss η r y t (fun i => ξ i.castSucc)) := ih.comp hrestr
      have hz : Measurable (fun ξ : Fin (t + 1) → FTRLSeed d =>
          ξ (Fin.last t)) := by fun_prop
      exact hL.add ((measurable_pureEstimator_seed (y t)).comp
        ((measurable_ftrlBallCandidate η r).comp hL |>.prodMk hz))

private lemma measurable_pureState {d : ℕ} (η r : ℝ)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
      borel (EuclideanSpace ℝ (Fin d))
    Measurable (pureState η r y t) := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  exact (measurable_ftrlBallCandidate η r).comp
    (measurable_pureCumLoss η r y t)

private lemma pureCumLoss_eq_sum
    {d : ℕ} {η r : ℝ} (hη : 0 < η) (hr0 : 0 < r) (hr1 : r < 1)
    {Ω : Type*} [MeasurableSpace Ω]
    (V : ℕ → Ω → ℝ) (W : ℕ → Ω → Fin d × Bool)
    (y : ℕ → EuclideanSpace ℝ (Fin d))
    (Abar A Yhat : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hftrl : ∀ ω, IsFTRLIterates η
      (fun b : EuclideanSpace ℝ (Fin d) => -Real.log (1 - ‖b‖) - ‖b‖)
      (Metric.ball 0 1) (Metric.closedBall 0 r)
      (fun t => Yhat t ω) (fun t => Abar t ω))
    (hA : ∀ t ω, A t ω =
      if V t ω < 1 - ‖Abar t ω‖ then signedDir (W t ω)
      else ‖Abar t ω‖⁻¹ • Abar t ω)
    (hY : ∀ t ω, Yhat t ω =
      (if V t ω < 1 - ‖Abar t ω‖ then
        d * ⟪A t ω, y t⟫ / (1 - ‖Abar t ω‖) else 0) • A t ω) :
    ∀ t ω, pureCumLoss η r y t
        (fun i : Fin t => (V i ω, W i ω)) =
      ∑ s ∈ Finset.range t, Yhat s ω := by
  intro t
  induction t with
  | zero => intro ω; simp [pureCumLoss]
  | succ t ih =>
      intro ω
      simp only [pureCumLoss]
      have hprefix : (fun i : Fin t =>
          (V (i.castSucc : Fin (t + 1)) ω, W (i.castSucc : Fin (t + 1)) ω)) =
          fun i : Fin t => (V i ω, W i ω) := by
        funext i
        rfl
      rw [hprefix, ih ω, Finset.sum_range_succ]
      have hb : Abar t ω = ftrlBallCandidate η r
          (∑ s ∈ Finset.range t, Yhat s ω) :=
        ftrlIterates_eq_candidate hη hr0 hr1
          (fun s => Yhat s ω) (fun s => Abar s ω) (hftrl ω) t
      rw [← hb]
      simp only [Fin.val_last]
      congr 1
      rw [hY t ω, hA t ω]
      rfl

private lemma Abar_eq_pureState
    {d : ℕ} {η r : ℝ} (hη : 0 < η) (hr0 : 0 < r) (hr1 : r < 1)
    {Ω : Type*} [MeasurableSpace Ω]
    (V : ℕ → Ω → ℝ) (W : ℕ → Ω → Fin d × Bool)
    (y : ℕ → EuclideanSpace ℝ (Fin d))
    (Abar A Yhat : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hftrl : ∀ ω, IsFTRLIterates η
      (fun b : EuclideanSpace ℝ (Fin d) => -Real.log (1 - ‖b‖) - ‖b‖)
      (Metric.ball 0 1) (Metric.closedBall 0 r)
      (fun t => Yhat t ω) (fun t => Abar t ω))
    (hA : ∀ t ω, A t ω =
      if V t ω < 1 - ‖Abar t ω‖ then signedDir (W t ω)
      else ‖Abar t ω‖⁻¹ • Abar t ω)
    (hY : ∀ t ω, Yhat t ω =
      (if V t ω < 1 - ‖Abar t ω‖ then
        d * ⟪A t ω, y t⟫ / (1 - ‖Abar t ω‖) else 0) • A t ω) :
    ∀ t ω, Abar t ω = pureState η r y t
      (fun i : Fin t => (V i ω, W i ω)) := by
  intro t ω
  rw [pureState, pureCumLoss_eq_sum hη hr0 hr1 V W y Abar A Yhat hftrl hA hY]
  exact ftrlIterates_eq_candidate hη hr0 hr1
    (fun s => Yhat s ω) (fun s => Abar s ω) (hftrl ω) t

private lemma Abar_indep_current_seed
    {d : ℕ} {η r : ℝ} (hη : 0 < η) (hr0 : 0 < r) (hr1 : r < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (V : ℕ → Ω → ℝ) (W : ℕ → Ω → Fin d × Bool)
    (hVmeas : ∀ t, Measurable (V t)) (hWmeas : ∀ t, Measurable (W t))
    (hindep : iIndepFun (fun t ω => (V t ω, W t ω)) P)
    (y : ℕ → EuclideanSpace ℝ (Fin d))
    (Abar A Yhat : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hftrl : ∀ ω, IsFTRLIterates η
      (fun b : EuclideanSpace ℝ (Fin d) => -Real.log (1 - ‖b‖) - ‖b‖)
      (Metric.ball 0 1) (Metric.closedBall 0 r)
      (fun t => Yhat t ω) (fun t => Abar t ω))
    (hA : ∀ t ω, A t ω =
      if V t ω < 1 - ‖Abar t ω‖ then signedDir (W t ω)
      else ‖Abar t ω‖⁻¹ • Abar t ω)
    (hY : ∀ t ω, Yhat t ω =
      (if V t ω < 1 - ‖Abar t ω‖ then
        d * ⟪A t ω, y t⟫ / (1 - ‖Abar t ω‖) else 0) • A t ω)
    (t : ℕ) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
      borel (EuclideanSpace ℝ (Fin d))
    IndepFun (Abar t) (fun ω => (V t ω, W t ω)) P := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  let S := Finset.range t
  let T : Finset ℕ := {t}
  have hST : Disjoint S T := by
    simp [S, T]
  have hseedMeas : ∀ s, Measurable (fun ω => (V s ω, W s ω)) :=
    fun s => (hVmeas s).prodMk (hWmeas s)
  have hbase : IndepFun
      (fun ω (i : S) => (V i ω, W i ω))
      (fun ω (i : T) => (V i ω, W i ω)) P :=
    iIndepFun.indepFun_finset S T hST hindep hseedMeas
  let φ : ((i : S) → FTRLSeed d) → EuclideanSpace ℝ (Fin d) :=
    fun ξ => pureState η r y t
      (fun j : Fin t => ξ ⟨j, Finset.mem_range.mpr j.isLt⟩)
  let ψ : ((i : T) → FTRLSeed d) → FTRLSeed d :=
    fun ξ => ξ ⟨t, Finset.mem_singleton_self t⟩
  have hφ : Measurable φ := by
    apply (measurable_pureState η r y t).comp
    fun_prop
  have hψ : Measurable ψ := by fun_prop
  have hc := hbase.comp hφ hψ
  apply hc.congr
  · filter_upwards [] with ω
    change φ (fun i : S => (V i ω, W i ω)) = Abar t ω
    rw [Abar_eq_pureState hη hr0 hr1 V W y Abar A Yhat hftrl hA hY t ω]
  · filter_upwards [] with ω
    rfl

private lemma map_W_eq_uniform_signed {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : Ω → Fin d × Bool) (hWmeas : Measurable W)
    (hW : ∀ u : Fin d × Bool,
      P {ω | W ω = u} = ((2 * d : ℕ) : ENNReal)⁻¹) :
    Measure.map W P = ((2 * d : ℕ) : ENNReal)⁻¹ • Measure.count := by
  apply Measure.ext_of_singleton
  intro u
  rw [Measure.map_apply hWmeas (measurableSet_singleton u)]
  change P {ω | W ω = u} = _
  rw [hW u]
  simp

private lemma map_current_seed {d : ℕ} (hd : 0 < d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → ℝ) (W : Ω → Fin d × Bool)
    (hVmeas : Measurable V) (hWmeas : Measurable W)
    (hVW : IndepFun V W P)
    (hV : Measure.map V P =
      (volume : Measure ℝ).restrict (Set.Icc 0 1))
    (hW : ∀ u : Fin d × Bool,
      P {ω | W ω = u} = ((2 * d : ℕ) : ENNReal)⁻¹) :
    Measure.map (fun ω => (V ω, W ω)) P =
      ((volume : Measure ℝ).restrict (Set.Icc 0 1)).prod
        (((2 * d : ℕ) : ENNReal)⁻¹ • Measure.count) := by
  rw [hVW.map_prod_eq_prod_map_map hVmeas.aemeasurable hWmeas.aemeasurable,
    hV, map_W_eq_uniform_signed hd P W hWmeas hW]

private lemma measurable_purePlay_seed {d : ℕ} :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
      borel (EuclideanSpace ℝ (Fin d))
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d =>
      purePlay z.1 z.2.1 z.2.2) := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  have hevent : MeasurableSet
      {z : EuclideanSpace ℝ (Fin d) × FTRLSeed d |
        z.2.1 < 1 - ‖z.1‖} :=
    measurableSet_lt measurable_snd.fst
      (measurable_const.sub measurable_fst.norm)
  have hsigned : Measurable
      (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d => signedDir z.2.2) :=
    (measurable_of_finite signedDir).comp measurable_snd.snd
  unfold purePlay
  exact Measurable.ite hevent hsigned
    (measurable_fst.norm.inv.smul measurable_fst)

private lemma ftrl_iterate_norm_lt_one
    {d : ℕ} {η r : ℝ} {Y Abar : ℕ → EuclideanSpace ℝ (Fin d)}
    (hftrl : IsFTRLIterates η
      (fun b : EuclideanSpace ℝ (Fin d) => -Real.log (1 - ‖b‖) - ‖b‖)
      (Metric.ball 0 1) (Metric.closedBall 0 r) Y Abar) :
    ∀ t, ‖Abar t‖ < 1 := by
  intro t
  have hmem : Abar t ∈ Metric.ball
      (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    cases t with
    | zero => exact hftrl.init_mem.2
    | succ t => exact hftrl.step_mem t |>.2
  simpa [Metric.mem_ball, dist_zero_right] using hmem

private lemma ftrl_iterate_norm_le_radius
    {d : ℕ} {η r : ℝ} {Y Abar : ℕ → EuclideanSpace ℝ (Fin d)}
    (hftrl : IsFTRLIterates η
      (fun b : EuclideanSpace ℝ (Fin d) => -Real.log (1 - ‖b‖) - ‖b‖)
      (Metric.ball 0 1) (Metric.closedBall 0 r) Y Abar) :
    ∀ t, ‖Abar t‖ ≤ r := by
  intro t
  have hmem : Abar t ∈ Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin d)) r := by
    cases t with
    | zero => exact hftrl.init_mem.1
    | succ t => exact hftrl.step_mem t |>.1
  simpa [Metric.mem_closedBall, dist_zero_right] using hmem

private lemma purePlay_norm_le_one {d : ℕ}
    (b : EuclideanSpace ℝ (Fin d)) (v : ℝ) (u : Fin d × Bool) :
    ‖purePlay b v u‖ ≤ 1 := by
  unfold purePlay
  split_ifs
  · have hu : ‖signedDir u‖ = 1 := signedSingle_norm u
    rw [hu]
  · by_cases hb : b = 0
    · simp [hb]
    · have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]

private lemma pureEstimator_norm_le {d : ℕ}
    (y b : EuclideanSpace ℝ (Fin d)) (v : ℝ) (u : Fin d × Bool)
    (hb : ‖b‖ < 1) :
    ‖pureEstimator y b v u‖ ≤ d * ‖y‖ / (1 - ‖b‖) := by
  have hp : 0 < 1 - ‖b‖ := by linarith
  unfold pureEstimator
  split_ifs with hv
  · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hp,
      abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
    have hi := abs_real_inner_le_norm (purePlay b v u) y
    have ha := purePlay_norm_le_one b v u
    have hprod : ‖purePlay b v u‖ * ‖y‖ ≤ ‖y‖ := by
      nlinarith [norm_nonneg y]
    have hinner : |⟪purePlay b v u, y⟫| ≤ ‖y‖ := hi.trans hprod
    have hplay := purePlay_norm_le_one b v u
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff_of_pos_right hp).2
    calc
      (d : ℝ) * |⟪purePlay b v u, y⟫| * ‖purePlay b v u‖ ≤
          (d : ℝ) * ‖y‖ * ‖purePlay b v u‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg d)) (norm_nonneg _)
      _ ≤ (d : ℝ) * ‖y‖ * 1 :=
        mul_le_mul_of_nonneg_left hplay
          (mul_nonneg (Nat.cast_nonneg d) (norm_nonneg y))
      _ = (d : ℝ) * ‖y‖ := by ring
  · simpa using
      (div_nonneg (mul_nonneg (Nat.cast_nonneg d) (norm_nonneg y)) hp.le)

private lemma integral_indep_seed
    {d : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ (Fin d))]
    [BorelSpace (EuclideanSpace ℝ (Fin d))]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (b : Ω → EuclideanSpace ℝ (Fin d))
    (Z : Ω → FTRLSeed d)
    (hbmeas : Measurable b) (hZmeas : Measurable Z)
    (hInd : IndepFun b Z P)
    (ν : Measure (FTRLSeed d)) [SFinite ν]
    (hZmap : Measure.map Z P = ν)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (F : EuclideanSpace ℝ (Fin d) × FTRLSeed d → G)
    (g : EuclideanSpace ℝ (Fin d) → G)
    (hFmeas : StronglyMeasurable F)
    (hFint : Integrable F ((Measure.map b P).prod ν))
    (hgood : ∀ᵐ x ∂(Measure.map b P), ‖x‖ < 1)
    (hinner : ∀ x, ‖x‖ < 1 → Integrable (fun z => F (x, z)) ν →
      ∫ z, F (x, z) ∂ν = g x) :
    ∫ ω, F (b ω, Z ω) ∂P = ∫ x, g x ∂(Measure.map b P) := by
  have hjoint : Measure.map (fun ω => (b ω, Z ω)) P =
      (Measure.map b P).prod ν := by
    rw [hInd.map_prod_eq_prod_map_map hbmeas.aemeasurable hZmeas.aemeasurable,
      hZmap]
  calc
    ∫ ω, F (b ω, Z ω) ∂P =
        ∫ z, F z ∂(Measure.map (fun ω => (b ω, Z ω)) P) := by
      symm
      exact integral_map (hbmeas.prodMk hZmeas).aemeasurable
        hFmeas.aestronglyMeasurable
    _ = ∫ z, F z ∂((Measure.map b P).prod ν) := by rw [hjoint]
    _ = ∫ x, ∫ z, F (x, z) ∂ν ∂(Measure.map b P) :=
      integral_prod F hFint
    _ = ∫ x, g x ∂(Measure.map b P) := by
      apply integral_congr_ae
      filter_upwards [hgood, hFint.prod_right_ae] with x hx hxi
      exact hinner x hx hxi

private lemma ftrl_round_moments
    {d : ℕ} (hd : 0 < d) {η r : ℝ} (hη : 0 < η)
    (hr : r = 1 - 2 * η * d) (hr0 : 0 < r) (hr1 : r < 1)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : ℕ → Ω → ℝ) (W : ℕ → Ω → Fin d × Bool)
    (hVmeas : ∀ t, Measurable (V t)) (hWmeas : ∀ t, Measurable (W t))
    (hVW : ∀ t, IndepFun (V t) (W t) P)
    (hV : ∀ t, Measure.map (V t) P =
      (volume : Measure ℝ).restrict (Set.Icc 0 1))
    (hW : ∀ t (u : Fin d × Bool),
      P {ω | W t ω = u} = ((2 * d : ℕ) : ENNReal)⁻¹)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (hy : ∀ t, ‖y t‖ ≤ 1)
    (Abar A Yhat : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hftrl : ∀ ω, IsFTRLIterates η
      (fun b : EuclideanSpace ℝ (Fin d) => -Real.log (1 - ‖b‖) - ‖b‖)
      (Metric.ball 0 1) (Metric.closedBall 0 r)
      (fun t => Yhat t ω) (fun t => Abar t ω))
    (hA' : ∀ t ω, A t ω =
      if V t ω < 1 - ‖Abar t ω‖ then signedDir (W t ω)
      else ‖Abar t ω‖⁻¹ • Abar t ω)
    (hY : ∀ t ω, Yhat t ω =
      (if V t ω < 1 - ‖Abar t ω‖ then
        d * ⟪A t ω, y t⟫ / (1 - ‖Abar t ω‖) else 0) • A t ω)
    (hAbarMeas : ∀ t, @Measurable Ω (EuclideanSpace ℝ (Fin d)) _
      (borel (EuclideanSpace ℝ (Fin d))) (Abar t))
    (hAMeas : ∀ t, @Measurable Ω (EuclideanSpace ℝ (Fin d)) _
      (borel (EuclideanSpace ℝ (Fin d))) (A t))
    (hYMeas : ∀ t, @Measurable Ω (EuclideanSpace ℝ (Fin d)) _
      (borel (EuclideanSpace ℝ (Fin d))) (Yhat t))
    (hInd : ∀ t,
      letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
        borel (EuclideanSpace ℝ (Fin d))
      IndepFun (Abar t) (fun ω => (V t ω, W t ω)) P)
    (t : ℕ) :
    (∫ ω, A t ω ∂P = ∫ ω, Abar t ω ∂P) ∧
    (∫ ω, Yhat t ω ∂P = y t) ∧
    (∫ ω, (1 - ‖Abar t ω‖) * ‖Yhat t ω‖ ^ 2 ∂P =
      d * ‖y t‖ ^ 2) ∧
    (∫ ω, ⟪Abar t ω, Yhat t ω⟫ ∂P =
      ∫ ω, ⟪Abar t ω, y t⟫ ∂P) := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  let μV := (volume : Measure ℝ).restrict (Set.Icc 0 1)
  let μW : Measure (Fin d × Bool) :=
    ((2 * d : ℕ) : ENNReal)⁻¹ • Measure.count
  let ν : Measure (FTRLSeed d) := μV.prod μW
  let Z : Ω → FTRLSeed d := fun ω => (V t ω, W t ω)
  have hZmeas : Measurable Z := (hVmeas t).prodMk (hWmeas t)
  have hZmap : Measure.map Z P = ν := by
    exact map_current_seed hd P (V t) (W t) (hVmeas t) (hWmeas t)
      (hVW t) (hV t) (hW t)
  letI : IsProbabilityMeasure ν := ⟨by
    rw [← hZmap, Measure.map_apply hZmeas MeasurableSet.univ]
    simp⟩
  have hgood : ∀ᵐ b ∂(Measure.map (Abar t) P), ‖b‖ < 1 := by
    rw [MeasureTheory.ae_map_iff (hAbarMeas t).aemeasurable
      (measurableSet_lt measurable_norm measurable_const)]
    exact Eventually.of_forall fun ω => ftrl_iterate_norm_lt_one (hftrl ω) t
  have hAnorm (ω : Ω) : ‖A t ω‖ ≤ 1 := by
    rw [hA' t ω]
    exact purePlay_norm_le_one (Abar t ω) (V t ω) (W t ω)
  have hAint : Integrable (A t) P :=
    Integrable.of_bound (hAMeas t).aestronglyMeasurable 1
      (Eventually.of_forall hAnorm)
  have hYnorm (ω : Ω) : ‖Yhat t ω‖ ≤ 1 / (2 * η) := by
    have hs := estimator_small hd hη hr
      (ftrl_iterate_norm_le_radius (hftrl ω) t) (hy t)
      (hA' t ω) (hY t ω)
    apply (le_div_iff₀ (by positivity : 0 < 2 * η)).2
    nlinarith [norm_nonneg (Yhat t ω)]
  have hYint : Integrable (Yhat t) P :=
    Integrable.of_bound (hYMeas t).aestronglyMeasurable (1 / (2 * η))
      (Eventually.of_forall hYnorm)
  let Q : Ω → ℝ := fun ω => (1 - ‖Abar t ω‖) * ‖Yhat t ω‖ ^ 2
  have hQmeas : Measurable Q :=
    (measurable_const.sub (hAbarMeas t).norm).mul ((hYMeas t).norm.pow_const 2)
  have hQbound (ω : Ω) : ‖Q ω‖ ≤ (1 / (2 * η)) ^ 2 := by
    have hb0 : 0 ≤ 1 - ‖Abar t ω‖ := by
      linarith [ftrl_iterate_norm_lt_one (hftrl ω) t]
    have hb1 : 1 - ‖Abar t ω‖ ≤ 1 := by linarith [norm_nonneg (Abar t ω)]
    have hC : 0 ≤ 1 / (2 * η) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb0 (sq_nonneg _))]
    calc
      (1 - ‖Abar t ω‖) * ‖Yhat t ω‖ ^ 2 ≤
          1 * ‖Yhat t ω‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hb1 (sq_nonneg _)
      _ ≤ (1 / (2 * η)) ^ 2 := by
        simpa using (sq_le_sq₀ (norm_nonneg (Yhat t ω)) hC).2 (hYnorm ω)
  have hQint : Integrable Q P :=
    Integrable.of_bound hQmeas.aestronglyMeasurable ((1 / (2 * η)) ^ 2)
      (Eventually.of_forall hQbound)
  have hjoint : Measure.map (fun ω => (Abar t ω, Z ω)) P =
      (Measure.map (Abar t) P).prod ν := by
    rw [(hInd t).map_prod_eq_prod_map_map (hAbarMeas t).aemeasurable
      hZmeas.aemeasurable, hZmap]
  have hplaycomp : (fun ω => purePlay (Abar t ω) (V t ω) (W t ω)) = A t := by
    funext ω
    exact (hA' t ω).symm
  have hestcomp : (fun ω =>
      pureEstimator (y t) (Abar t ω) (V t ω) (W t ω)) = Yhat t := by
    funext ω
    rw [hY t ω, hA' t ω]
    rfl
  have hsqcomp : (fun ω => (1 - ‖Abar t ω‖) *
      ‖pureEstimator (y t) (Abar t ω) (V t ω) (W t ω)‖ ^ 2) = Q := by
    funext ω
    rw [congrFun hestcomp ω]
  have hplayFint : Integrable
      (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d =>
        purePlay z.1 z.2.1 z.2.2) ((Measure.map (Abar t) P).prod ν) := by
    rw [← hjoint]
    apply (integrable_map_measure
      (measurable_purePlay_seed (d := d)).aestronglyMeasurable
      ((hAbarMeas t).prodMk hZmeas).aemeasurable).2
    change Integrable (fun ω => purePlay (Abar t ω) (V t ω) (W t ω)) P
    rw [hplaycomp]
    exact hAint
  have hestFint : Integrable
      (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d =>
        pureEstimator (y t) z.1 z.2.1 z.2.2)
      ((Measure.map (Abar t) P).prod ν) := by
    rw [← hjoint]
    apply (integrable_map_measure
      (measurable_pureEstimator_seed (y t)).aestronglyMeasurable
      ((hAbarMeas t).prodMk hZmeas).aemeasurable).2
    change Integrable
      (fun ω => pureEstimator (y t) (Abar t ω) (V t ω) (W t ω)) P
    rw [hestcomp]
    exact hYint
  have hsqFmeas : StronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d =>
        (1 - ‖z.1‖) * ‖pureEstimator (y t) z.1 z.2.1 z.2.2‖ ^ 2) :=
    ((measurable_const.sub measurable_fst.norm).mul
      ((measurable_pureEstimator_seed (y t)).norm.pow_const 2)).stronglyMeasurable
  have hsqFint : Integrable
      (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d =>
        (1 - ‖z.1‖) * ‖pureEstimator (y t) z.1 z.2.1 z.2.2‖ ^ 2)
      ((Measure.map (Abar t) P).prod ν) := by
    rw [← hjoint]
    apply (integrable_map_measure hsqFmeas.aestronglyMeasurable
      ((hAbarMeas t).prodMk hZmeas).aemeasurable).2
    change Integrable (fun ω => (1 - ‖Abar t ω‖) *
      ‖pureEstimator (y t) (Abar t ω) (V t ω) (W t ω)‖ ^ 2) P
    rw [hsqcomp]
    exact hQint
  have hmapRealUniv : (Measure.map (Abar t) P).real Set.univ = 1 := by
    rw [measureReal_def]
    rw [Measure.map_apply (hAbarMeas t) MeasurableSet.univ]
    simp
  let H : Ω → ℝ := fun ω => ⟪Abar t ω, Yhat t ω⟫
  have hHmeas : Measurable H := Measurable.inner (hAbarMeas t) (hYMeas t)
  have hHint : Integrable H P := by
    apply Integrable.of_bound hHmeas.aestronglyMeasurable
      (r * (1 / (2 * η)))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    calc
      |⟪Abar t ω, Yhat t ω⟫| ≤ ‖Abar t ω‖ * ‖Yhat t ω‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ r * (1 / (2 * η)) := mul_le_mul
        (ftrl_iterate_norm_le_radius (hftrl ω) t) (hYnorm ω)
        (norm_nonneg _) (le_of_lt hr0)
  have hinnerFmeas : StronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d =>
        ⟪z.1, pureEstimator (y t) z.1 z.2.1 z.2.2⟫) :=
    (Measurable.inner measurable_fst
      (measurable_pureEstimator_seed (y t))).stronglyMeasurable
  have hinnercomp : (fun ω =>
      ⟪Abar t ω, pureEstimator (y t) (Abar t ω) (V t ω) (W t ω)⟫) = H := by
    funext ω
    rw [congrFun hestcomp ω]
  have hinnerFint : Integrable
      (fun z : EuclideanSpace ℝ (Fin d) × FTRLSeed d =>
        ⟪z.1, pureEstimator (y t) z.1 z.2.1 z.2.2⟫)
      ((Measure.map (Abar t) P).prod ν) := by
    rw [← hjoint]
    apply (integrable_map_measure hinnerFmeas.aestronglyMeasurable
      ((hAbarMeas t).prodMk hZmeas).aemeasurable).2
    change Integrable (fun ω =>
      ⟪Abar t ω, pureEstimator (y t) (Abar t ω) (V t ω) (W t ω)⟫) P
    rw [hinnercomp]
    exact hHint
  constructor
  · have hp := integral_indep_seed P (Abar t) Z (hAbarMeas t) hZmeas
        (hInd t) ν hZmap
        (fun z => purePlay z.1 z.2.1 z.2.2) id
        (measurable_purePlay_seed (d := d)).stronglyMeasurable
        hplayFint hgood (fun b hb hbi => by
          rw [integral_prod_symm _ hbi]
          exact iterated_integral_purePlay hd b hb)
    rw [← hplaycomp, hp]
    exact integral_map (hAbarMeas t).aemeasurable
      stronglyMeasurable_id.aestronglyMeasurable
  constructor
  · have he := integral_indep_seed P (Abar t) Z (hAbarMeas t) hZmeas
        (hInd t) ν hZmap
        (fun z => pureEstimator (y t) z.1 z.2.1 z.2.2) (fun _ => y t)
        (measurable_pureEstimator_seed (y t)).stronglyMeasurable
        hestFint hgood (fun b hb hbi => by
          rw [integral_prod_symm _ hbi]
          exact iterated_integral_pureEstimator hd (y t) b hb)
    rw [← hestcomp, he]
    rw [integral_const, hmapRealUniv, one_smul]
  constructor
  · have hs := integral_indep_seed P (Abar t) Z (hAbarMeas t) hZmeas
        (hInd t) ν hZmap
        (fun z => (1 - ‖z.1‖) *
          ‖pureEstimator (y t) z.1 z.2.1 z.2.2‖ ^ 2)
        (fun _ => d * ‖y t‖ ^ 2) hsqFmeas hsqFint hgood
        (fun b hb hbi => by
          rw [integral_prod_symm _ hbi]
          exact iterated_integral_pureEstimator_sq hd (y t) b hb)
    have hsqactual : (fun ω => (1 - ‖Abar t ω‖) * ‖Yhat t ω‖ ^ 2) =
        fun ω => (1 - ‖Abar t ω‖) *
          ‖pureEstimator (y t) (Abar t ω) (V t ω) (W t ω)‖ ^ 2 := by
      funext ω
      rw [congrFun hestcomp ω]
    rw [hsqactual, hs, integral_const, hmapRealUniv]
    simp
  · have hi := integral_indep_seed P (Abar t) Z (hAbarMeas t) hZmeas
        (hInd t) ν hZmap
        (fun z => ⟪z.1, pureEstimator (y t) z.1 z.2.1 z.2.2⟫)
        (fun b => ⟪b, y t⟫) hinnerFmeas hinnerFint hgood
        (fun b hb _ => by
          have hvmeas : StronglyMeasurable (fun z : FTRLSeed d =>
              pureEstimator (y t) b z.1 z.2) :=
            ((measurable_pureEstimator_seed (y t)).comp
              (measurable_const.prodMk measurable_id)).stronglyMeasurable
          have hvint : Integrable (fun z : FTRLSeed d =>
              pureEstimator (y t) b z.1 z.2) ν :=
            Integrable.of_bound hvmeas.aestronglyMeasurable
              (d * ‖y t‖ / (1 - ‖b‖))
              (Eventually.of_forall fun z =>
                pureEstimator_norm_le (y t) b z.1 z.2 hb)
          rw [integral_inner hvint b]
          congr 1
          rw [integral_prod_symm _ hvint]
          exact iterated_integral_pureEstimator hd (y t) b hb)
    calc
      ∫ ω, ⟪Abar t ω, Yhat t ω⟫ ∂P =
          ∫ ω, ⟪Abar t ω,
            pureEstimator (y t) (Abar t ω) (V t ω) (W t ω)⟫ ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [congrFun hestcomp ω]
      _ = ∫ b, ⟪b, y t⟫ ∂(Measure.map (Abar t) P) := hi
      _ = ∫ ω, ⟪Abar t ω, y t⟫ ∂P :=
        integral_map (hAbarMeas t).aemeasurable
          ((Measurable.inner measurable_id measurable_const).stronglyMeasurable.aestronglyMeasurable)

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (hy : ∀ t, ‖y t‖ ≤ 1)
    (η r : ℝ) (hη0 : 0 < η)
    (hr : r = 1 - 2 * η * d) (hr0 : 0 < r)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : ℕ → Ω → ℝ) (W : ℕ → Ω → Fin d × Bool)
    (hVmeas : ∀ t, Measurable (V t)) (hWmeas : ∀ t, Measurable (W t))
    (hindep : iIndepFun (fun t ω => (V t ω, W t ω)) P)
    (hVW : ∀ t, IndepFun (V t) (W t) P)
    (hV : ∀ t, Measure.map (V t) P = (volume : Measure ℝ).restrict (Set.Icc 0 1))
    (hW : ∀ t (u : Fin d × Bool), P {ω | W t ω = u} = ((2 * d : ℕ) : ENNReal)⁻¹)
    (Abar A Yhat : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hftrl : ∀ ω, IsFTRLIterates η
      (fun b : EuclideanSpace ℝ (Fin d) => -Real.log (1 - ‖b‖) - ‖b‖)
      (Metric.ball 0 1) (Metric.closedBall 0 r)
      (fun t => Yhat t ω) (fun t => Abar t ω))
    (hA : ∀ t ω, A t ω =
      if V t ω < 1 - ‖Abar t ω‖ then
        (if (W t ω).2 then (1 : ℝ) else -1) • EuclideanSpace.single (W t ω).1 1
      else ‖Abar t ω‖⁻¹ • Abar t ω)
    (hY : ∀ t ω, Yhat t ω =
      (if V t ω < 1 - ‖Abar t ω‖ then
        d * ⟪A t ω, y t⟫ / (1 - ‖Abar t ω‖) else 0) • A t ω) :
    ∀ a₀ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∫ ω, oloRegret (fun t => A t ω) y n a₀ ∂P ≤
        (1 - r) * n + Real.log (1 / (1 - r)) / η + η * n * d := by
  intro a₀ ha₀
  have hr1 : r < 1 := by
    rw [hr]
    have hpos : 0 < 2 * η * (d : ℝ) := by positivity
    linarith
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
    borel (EuclideanSpace ℝ (Fin d))
  letI : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩
  have hA' : ∀ t ω, A t ω =
      if V t ω < 1 - ‖Abar t ω‖ then BanditAlgorithm.signedDir (W t ω)
      else ‖Abar t ω‖⁻¹ • Abar t ω := by
    intro t ω
    simpa [BanditAlgorithm.signedDir] using hA t ω
  have hproc := BanditAlgorithm.ftrlProcess_measurable hη0 hr0 hr1
    V W hVmeas hWmeas y Abar A Yhat hftrl hA hY
  rcases hproc with ⟨hAbarMeas, hAMeas, hYMeas⟩
  have hInd (t : ℕ) : IndepFun (Abar t) (fun ω => (V t ω, W t ω)) P :=
    BanditAlgorithm.Abar_indep_current_seed hη0 hr0 hr1 P V W hVmeas hWmeas
      hindep y Abar A Yhat hftrl hA' hY t
  have hmom (t : ℕ) := BanditAlgorithm.ftrl_round_moments hd hη0 hr hr0 hr1
    P V W hVmeas hWmeas hVW hV hW y hy Abar A Yhat hftrl hA' hY
    hAbarMeas hAMeas hYMeas hInd t
  have hAbarNorm (t : ℕ) (ω : Ω) : ‖Abar t ω‖ ≤ r :=
    BanditAlgorithm.ftrl_iterate_norm_le_radius (hftrl ω) t
  have hAbarInt (t : ℕ) : Integrable (Abar t) P :=
    Integrable.of_bound (hAbarMeas t).aestronglyMeasurable r
      (Eventually.of_forall (hAbarNorm t))
  have hAnorm (t : ℕ) (ω : Ω) : ‖A t ω‖ ≤ 1 := by
    rw [hA' t ω]
    exact BanditAlgorithm.purePlay_norm_le_one (Abar t ω) (V t ω) (W t ω)
  have hAint (t : ℕ) : Integrable (A t) P :=
    Integrable.of_bound (hAMeas t).aestronglyMeasurable 1
      (Eventually.of_forall (hAnorm t))
  have hYnorm (t : ℕ) (ω : Ω) : ‖Yhat t ω‖ ≤ 1 / (2 * η) := by
    have hs := BanditAlgorithm.estimator_small hd hη0 hr (hAbarNorm t ω)
      (hy t) (hA' t ω) (hY t ω)
    apply (le_div_iff₀ (by positivity : 0 < 2 * η)).2
    nlinarith [norm_nonneg (Yhat t ω)]
  have hYint (t : ℕ) : Integrable (Yhat t) P :=
    Integrable.of_bound (hYMeas t).aestronglyMeasurable (1 / (2 * η))
      (Eventually.of_forall (hYnorm t))
  have hCrossInt (t : ℕ) : Integrable
      (fun ω => ⟪Abar t ω, Yhat t ω⟫) P := by
    apply Integrable.of_bound
      (Measurable.inner (hAbarMeas t) (hYMeas t)).aestronglyMeasurable
      (r * (1 / (2 * η)))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hAbarNorm t ω) (hYnorm t ω) (norm_nonneg _) (le_of_lt hr0))
  have hActualTermInt (t : ℕ) : Integrable
      (fun ω => ⟪A t ω - a₀, y t⟫) P :=
    ((hAint t).sub (integrable_const a₀)).inner_const (y t)
  have hPseudoTermInt (t : ℕ) : Integrable
      (fun ω => ⟪Abar t ω - a₀, y t⟫) P :=
    ((hAbarInt t).sub (integrable_const a₀)).inner_const (y t)
  have hRhatTermInt (t : ℕ) : Integrable
      (fun ω => ⟪Abar t ω - r • a₀, Yhat t ω⟫) P := by
    simpa only [inner_sub_left, Pi.sub_def] using
      (hCrossInt t).sub ((hYint t).const_inner (r • a₀))
  let Q : ℕ → Ω → ℝ :=
    fun t ω => (1 - ‖Abar t ω‖) * ‖Yhat t ω‖ ^ 2
  have hQint (t : ℕ) : Integrable (Q t) P := by
    have hQmeas : Measurable (Q t) :=
      (measurable_const.sub (hAbarMeas t).norm).mul ((hYMeas t).norm.pow_const 2)
    apply Integrable.of_bound hQmeas.aestronglyMeasurable ((1 / (2 * η)) ^ 2)
    filter_upwards [] with ω
    have hb0 : 0 ≤ 1 - ‖Abar t ω‖ := by
      linarith [BanditAlgorithm.ftrl_iterate_norm_lt_one (hftrl ω) t]
    have hb1 : 1 - ‖Abar t ω‖ ≤ 1 := by linarith [norm_nonneg (Abar t ω)]
    have hC : 0 ≤ 1 / (2 * η) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb0 (sq_nonneg _))]
    calc
      (1 - ‖Abar t ω‖) * ‖Yhat t ω‖ ^ 2 ≤ ‖Yhat t ω‖ ^ 2 := by
        nlinarith [sq_nonneg (‖Yhat t ω‖)]
      _ ≤ (1 / (2 * η)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hC).2 (hYnorm t ω)
  let Rhat : Ω → ℝ := fun ω =>
    oloRegret (fun t => Abar t ω) (fun t => Yhat t ω) n (r • a₀)
  have hRhatInt : Integrable Rhat P := by
    unfold Rhat oloRegret
    apply integrable_finsetSum
    intro t ht
    exact hRhatTermInt t
  let B : Ω → ℝ := fun ω =>
    Real.log (1 / (1 - r)) / η + η * ∑ t ∈ Finset.range n, Q t ω
  have hBInt : Integrable B P := by
    have hc : Integrable (fun _ : Ω => Real.log (1 / (1 - r)) / η) P :=
      integrable_const _
    have hs : Integrable (fun ω => ∑ t ∈ Finset.range n, Q t ω) P :=
      integrable_finsetSum _ fun t _ => hQint t
    exact hc.add (hs.const_mul η)
  have hpath : ∀ ω, Rhat ω ≤ B ω := by
    intro ω
    exact BanditAlgorithm.ftrl_pathwise_regret_bound hd hη0 hr hr0 y hy
      (fun t => V t ω) (fun t => W t ω) (fun t => Abar t ω)
      (fun t => A t ω) (fun t => Yhat t ω) (hftrl ω)
      (fun t => hA t ω) (fun t => hY t ω) a₀ ha₀
  have hERhat_le : ∫ ω, Rhat ω ∂P ≤
      Real.log (1 / (1 - r)) / η + η * n * d := by
    have hmono : ∫ ω, Rhat ω ∂P ≤ ∫ ω, B ω ∂P :=
      integral_mono hRhatInt hBInt hpath
    rw [show (∫ ω, B ω ∂P) =
        Real.log (1 / (1 - r)) / η +
          η * ∑ t ∈ Finset.range n, d * ‖y t‖ ^ 2 by
      unfold B
      have hc : Integrable (fun _ : Ω => Real.log (1 / (1 - r)) / η) P :=
        integrable_const _
      have hs : Integrable (fun ω => ∑ t ∈ Finset.range n, Q t ω) P :=
        integrable_finsetSum _ fun t _ => hQint t
      rw [integral_add hc (hs.const_mul η),
        integral_const, probReal_univ, one_smul,
        integral_const_mul, integral_finsetSum _ (fun t _ => hQint t)]
      congr 2
      apply Finset.sum_congr rfl
      intro t ht
      exact (hmom t).2.2.1] at hmono
    calc
      ∫ ω, Rhat ω ∂P ≤
          Real.log (1 / (1 - r)) / η + η * ∑ t ∈ Finset.range n, d * ‖y t‖ ^ 2 := hmono
      _ ≤ Real.log (1 / (1 - r)) / η + η * n * d := by
        have hsum : ∑ t ∈ Finset.range n, (d : ℝ) * ‖y t‖ ^ 2 ≤ n * d := by
          calc
            ∑ t ∈ Finset.range n, (d : ℝ) * ‖y t‖ ^ 2 ≤
                ∑ _t ∈ Finset.range n, (d : ℝ) := by
              apply Finset.sum_le_sum
              intro t ht
              simpa using mul_le_mul_of_nonneg_left
                ((sq_le_sq₀ (norm_nonneg (y t)) (by norm_num)).2 (hy t))
                (Nat.cast_nonneg d)
            _ = n * d := by simp
        nlinarith [le_of_lt hη0]
  have hEAeq :
      ∫ ω, oloRegret (fun t => A t ω) y n a₀ ∂P =
      ∫ ω, oloRegret (fun t => Abar t ω) y n a₀ ∂P := by
    unfold oloRegret
    rw [integral_finsetSum _ (fun t _ => hActualTermInt t),
      integral_finsetSum _ (fun t _ => hPseudoTermInt t)]
    apply Finset.sum_congr rfl
    intro t ht
    calc
      ∫ ω, ⟪A t ω - a₀, y t⟫ ∂P =
          ⟪y t, ∫ ω, A t ω - a₀ ∂P⟫ := by
        rw [show (∫ ω, ⟪A t ω - a₀, y t⟫ ∂P) =
            ∫ ω, ⟪y t, A t ω - a₀⟫ ∂P by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact real_inner_comm _ _]
        exact integral_inner ((hAint t).sub (integrable_const a₀)) (y t)
      _ = ⟪y t, ∫ ω, Abar t ω - a₀ ∂P⟫ := by
        rw [integral_sub (hAint t) (integrable_const a₀),
          integral_sub (hAbarInt t) (integrable_const a₀), (hmom t).1]
      _ = ∫ ω, ⟪Abar t ω - a₀, y t⟫ ∂P := by
        rw [show (∫ ω, ⟪Abar t ω - a₀, y t⟫ ∂P) =
            ∫ ω, ⟪y t, Abar t ω - a₀⟫ ∂P by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact real_inner_comm _ _]
        exact (integral_inner ((hAbarInt t).sub (integrable_const a₀)) (y t)).symm
  have ha₀norm : ‖a₀‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using ha₀
  have hroundcomp (t : ℕ) :
      ∫ ω, ⟪Abar t ω - a₀, y t⟫ ∂P ≤
        ∫ ω, ⟪Abar t ω - r • a₀, Yhat t ω⟫ ∂P + (1 - r) := by
    have hleft : ∫ ω, ⟪Abar t ω - a₀, y t⟫ ∂P =
        (∫ ω, ⟪Abar t ω, y t⟫ ∂P) - ⟪a₀, y t⟫ := by
      simp_rw [inner_sub_left]
      rw [integral_sub ((hAbarInt t).inner_const (y t)) (integrable_const _)]
      simp
    have hright : ∫ ω, ⟪Abar t ω - r • a₀, Yhat t ω⟫ ∂P =
        (∫ ω, ⟪Abar t ω, y t⟫ ∂P) - ⟪r • a₀, y t⟫ := by
      simp_rw [inner_sub_left]
      rw [integral_sub (hCrossInt t) ((hYint t).const_inner (r • a₀)),
        integral_inner (hYint t) (r • a₀), (hmom t).2.1,
        (hmom t).2.2.2]
    rw [hleft, hright, real_inner_smul_left]
    have habs : |⟪a₀, y t⟫| ≤ 1 :=
      (abs_real_inner_le_norm a₀ (y t)).trans (by
        nlinarith [norm_nonneg a₀, norm_nonneg (y t), hy t])
    have hc : -1 ≤ ⟪a₀, y t⟫ := (neg_le_of_abs_le habs)
    nlinarith
  have hEPseudo_le :
      ∫ ω, oloRegret (fun t => Abar t ω) y n a₀ ∂P ≤
        ∫ ω, Rhat ω ∂P + (1 - r) * n := by
    unfold Rhat oloRegret
    rw [integral_finsetSum _ (fun t _ => hPseudoTermInt t),
      integral_finsetSum _ (fun t _ => hRhatTermInt t)]
    calc
      ∑ t ∈ Finset.range n, ∫ ω, ⟪Abar t ω - a₀, y t⟫ ∂P ≤
          ∑ t ∈ Finset.range n,
            ((∫ ω, ⟪Abar t ω - r • a₀, Yhat t ω⟫ ∂P) + (1 - r)) := by
        apply Finset.sum_le_sum
        intro t ht
        exact hroundcomp t
      _ = (∑ t ∈ Finset.range n,
            ∫ ω, ⟪Abar t ω - r • a₀, Yhat t ω⟫ ∂P) +
          (1 - r) * n := by
        rw [Finset.sum_add_distrib]
        simp
        ring
  rw [hEAeq]
  calc
    ∫ ω, oloRegret (fun t => Abar t ω) y n a₀ ∂P ≤
        ∫ ω, Rhat ω ∂P + (1 - r) * n := hEPseudo_le
    _ ≤ (Real.log (1 / (1 - r)) / η + η * n * d) + (1 - r) * n := by
      linarith
    _ = (1 - r) * n + Real.log (1 / (1 - r)) / η + η * n * d := by ring
