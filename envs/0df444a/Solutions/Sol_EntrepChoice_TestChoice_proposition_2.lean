-- Prove2me | solution 1 for EntrepChoice.TestChoice.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T16:07:38.552252+00:00
-- url     : https://prove2.me/submissions/a2c39fad-d3d8-48c7-bcd8-613a37bf4c05

import Mathlib
import Definitions.Def_EntrepChoice_TestChoice_Setting

set_option autoImplicit false

open EntrepChoice.TestChoice in
theorem solution (P : Params) (hP : Standing P) (lv ls : ℝ)
    (hlv : 0 ≤ lv ∧ lv ≤ 1) (hls : 0 ≤ ls ∧ ls ≤ 1)
    (hA_strat : A1 P ⟨lv, 1⟩) (hA_idea : A1 P ⟨1, ls⟩)
    (hcond : (1 - lv) * P.p0 * (1 - P.e0) * (P.e0 * P.v - P.C)
               < (1 - P.p0) * P.e0 * (1 - ls) * P.C) :
    testValue P ⟨1, ls⟩ < testValue P ⟨lv, 1⟩ := by
  obtain ⟨hp0, hp1, he0, he1, hv, hV, _hc⟩ := hP
  obtain ⟨hlv0, hlv1⟩ := hlv
  obtain ⟨hls0, hls1⟩ := hls
  have hC : P.C = P.e0 * P.p0 * P.v := by linarith
  have hCpos : 0 < P.C := by rw [hC]; positivity
  have hgap : 0 < P.e0 * P.v - P.C := by
    rw [hC]; have : 0 < P.e0 * P.v * (1 - P.p0) := by
      apply mul_pos (mul_pos he0 hv); linarith
    nlinarith
  -- (A1) for the idea-biased test at signal (H,B)
  have hb := hA_idea.hb_idea
  simp only [sigMass, ideaMass, sumStates, joint, sigProb, prior] at hb
  have h1 : P.p0 * (1 - P.e0) + (1 - P.p0) * P.e0 * (1 - ls) ≤ 1 - P.e0 := by
    by_contra h
    push_neg at h
    have := mul_lt_mul_of_pos_left h hp0
    nlinarith
  have h2 : P.e0 * (1 - ls) ≤ 1 - P.e0 := by
    by_contra h
    push_neg at h
    have := mul_lt_mul_of_pos_left h (show (0:ℝ) < 1 - P.p0 by linarith)
    nlinarith
  -- switching after (H,B) is optimal for the idea-biased test
  have hsw : 0 ≤ P.p0 * (1 - P.e0) * (P.e0 * P.v - P.C) - (1 - P.p0) * P.e0 * (1 - ls) * P.C := by
    rw [hC]
    have hk : 0 ≤ P.p0 * P.e0 * P.v * (1 - P.p0) := by
      apply mul_nonneg (by positivity); linarith
    have : P.p0 * (1 - P.e0) * (P.e0 * P.v - P.e0 * P.p0 * P.v)
        - (1 - P.p0) * P.e0 * (1 - ls) * (P.e0 * P.p0 * P.v)
        = (P.p0 * P.e0 * P.v * (1 - P.p0)) * ((1 - P.e0) - P.e0 * (1 - ls)) := by ring
    rw [this]
    exact mul_nonneg hk (by linarith)
  -- closed forms of the action values
  have eHG : bestVal P ⟨1, ls⟩ .HG = bestVal P ⟨lv, 1⟩ .HG := by
    simp [bestVal, actVal, sumStates, joint, sigProb, prior, payoff]
  have uHB : bestVal P ⟨1, ls⟩ .HB
      ≤ P.p0 * (1 - P.e0) * (P.e0 * P.v - P.C) - (1 - P.p0) * P.e0 * (1 - ls) * P.C := by
    simp only [bestVal, actVal, sumStates, joint, sigProb, prior, payoff]
    refine max_le ?_ (max_le ?_ ?_)
    · have : 0 ≤ 1 - ls := by linarith
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 1 - P.p0 by linarith) he0.le) this)
        hCpos.le, mul_pos (mul_pos hp0 (show (0:ℝ) < 1 - P.e0 by linarith)) hv]
    · linarith
    · simpa using hsw
  have uLG : bestVal P ⟨1, ls⟩ .LG ≤ 0 := by
    simp only [bestVal, actVal, sumStates, joint, sigProb, prior, payoff]
    have : 0 ≤ (1 - P.p0) * P.e0 * ls * P.C :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) he0.le) hls0) hCpos.le
    refine max_le ?_ (max_le ?_ ?_) <;> nlinarith
  have uLB : bestVal P ⟨1, ls⟩ .LB ≤ 0 := by
    simp only [bestVal, actVal, sumStates, joint, sigProb, prior, payoff]
    have : 0 ≤ (1 - P.p0) * (1 - P.e0) * P.C :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hCpos.le
    refine max_le ?_ (max_le ?_ ?_) <;> nlinarith
  have lHB : lv * (P.p0 * (1 - P.e0) * (P.e0 * P.v - P.C)) ≤ bestVal P ⟨lv, 1⟩ .HB := by
    unfold bestVal
    refine le_trans ?_ (le_max_of_le_right (le_max_left _ _))
    simp only [actVal, sumStates, joint, sigProb, prior, payoff]
    ring_nf
    rfl
  have lLG : 0 ≤ bestVal P ⟨lv, 1⟩ .LG := by
    unfold bestVal
    refine le_trans ?_ (le_max_of_le_right (le_max_right _ _))
    simp [actVal, sumStates, payoff]
  have lLB : 0 ≤ bestVal P ⟨lv, 1⟩ .LB := by
    unfold bestVal
    refine le_trans ?_ (le_max_of_le_right (le_max_right _ _))
    simp [actVal, sumStates, payoff]
  unfold testValue
  rw [eHG]
  nlinarith
