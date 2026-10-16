-- Prove2me | solution 1 for CourierDispatch.Exogenous.unique_root
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:28:57.478802+00:00
-- url     : https://prove2.me/submissions/45fd1bb3-0f22-427f-b803-2dec139ffbc6

import Mathlib
import Definitions.Def_CourierDispatch_Exogenous_Setting

open CourierDispatch.Exogenous

namespace CourierResearch

noncomputable def poly (C a : ℝ) : ℝ :=
  (24*C-26*TB)*a^3+(26*TB^2-18*C-6*TB)*a^2+(6*TB^2+9*TB)*a-9*TB^2

theorem TB_bounds : (89/100 : ℝ) < TB ∧ TB < 9/10 := by
  have hp := Real.pi_pos
  have hden : 0 < 2*(32+15*Real.pi) := by positivity
  unfold TB
  constructor
  · apply (lt_div_iff₀ hden).2
    linarith [Real.pi_gt_d2]
  · apply (div_lt_iff₀ hden).2
    linarith [Real.pi_lt_d2]

theorem poly_derivative (C x : ℝ) :
    HasDerivAt (poly C) ((72*C-78*TB)*x^2+(52*TB^2-36*C-12*TB)*x+(6*TB^2+9*TB)) x := by
  convert! ((((hasDerivAt_id x).pow 3).const_mul (24*C-26*TB)).add
    (((hasDerivAt_id x).pow 2).const_mul (26*TB^2-18*C-6*TB))).add
    ((hasDerivAt_id x).const_mul (6*TB^2+9*TB)) |>.sub_const (9*TB^2) using 1
  simp only [id_eq]
  ring

theorem poly_increasing (C : ℝ) (hC : CBRange C) :
    StrictMonoOn (poly C) (Set.Icc 0 TD) := by
  have hT := TB_bounds
  have hsq : (89/100 : ℝ)^2 ≤ TB^2 := by nlinarith [hT.1]
  have hA : 72*C-78*TB ≤ 0 := by rcases hC with ⟨_,hC⟩; linarith [hT.1]
  have hcoef : -12 ≤ (72*C-78*TB)*(3/4)+(52*TB^2-36*C-12*TB) := by
    rcases hC with ⟨hC,_⟩
    nlinarith only [hC,hsq,hT.2]
  have hconst : 12 < 6*TB^2+9*TB := by nlinarith only [hsq,hT.1]
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 TD)
  · exact fun x _ => (poly_derivative C x).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Icc 0 TD := interior_subset hx
    have hxlo := hx'.1
    have hxhi : x ≤ 3/4 := hx'.2
    rw [(poly_derivative C x).deriv]
    have hxx : x^2 ≤ (3/4)*x := by nlinarith
    have h1 := mul_le_mul_of_nonpos_left hxx hA
    have h2 := mul_le_mul_of_nonneg_right hcoef hxlo
    nlinarith only [h1,h2,hconst,hxhi]

theorem poly_endpoints (C : ℝ) (hC : CBRange C) :
    poly C (56/100) < 0 ∧ 0 < poly C (58/100) := by
  have hT := TB_bounds
  have hlo : (89/100 : ℝ)^2 ≤ TB^2 := by nlinarith [hT.1]
  have hhi : TB^2 ≤ (9/10 : ℝ)^2 := by nlinarith [hT.1,hT.2]
  rcases hC with ⟨hClo,hChi⟩
  unfold poly
  constructor <;> nlinarith only [hT.1,hT.2,hlo,hhi,hClo,hChi]

theorem fA_eq (C a : ℝ) (_ha : 0 ≤ a) (haT : a < TD) :
    fA C a = poly C a/(6*TB*(3-4*a)*(TB-a)) := by
  have hT := TB_bounds
  have hTB : TB ≠ 0 := by linarith [hT.1]
  have hTD : 3-4*a ≠ 0 := by unfold TD at haT; linarith
  have hdiff : TB-a ≠ 0 := by unfold TD at haT; linarith [hT.1]
  have hTD' : (3 : ℝ)-a*4 ≠ 0 := by unfold TD at haT; linarith
  have hD : (3/4 : ℝ)-a ≠ 0 := by unfold TD at haT; linarith
  unfold fA poly CD TD
  field_simp [hTB,hTD,hTD',hdiff,hD]
  ring

end CourierResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mingliu Chen and Ming Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063.
theorem solution (CB : ℝ) (hCB : CBRange CB) :
    ∃ a₁ : ℝ, 0 < a₁ ∧ a₁ < TD ∧ 56 / 100 < a₁ ∧ a₁ < 58 / 100 ∧ fA CB a₁ = 0 ∧
      (∀ a : ℝ, 0 < a → a < a₁ → fA CB a < 0) ∧
      (∀ a : ℝ, a₁ < a → a < TD → 0 < fA CB a) := by
  obtain ⟨hl,hu⟩ := CourierResearch.poly_endpoints CB hCB
  have hc : Continuous (CourierResearch.poly CB) := by unfold CourierResearch.poly; fun_prop
  obtain ⟨r,hr,he⟩ := intermediate_value_Icc (by norm_num : (56/100 : ℝ) ≤ 58/100)
    hc.continuousOn ⟨hl.le,hu.le⟩
  have hrlo : (56/100 : ℝ) < r := by
    by_contra h
    have heq : r=56/100 := le_antisymm (le_of_not_gt h) hr.1
    have hh := he
    rw [heq] at hh
    linarith only [hl,hh]
  have hrhi : r < (58/100 : ℝ) := by
    by_contra h
    have heq : r=58/100 := le_antisymm hr.2 (le_of_not_gt h)
    have hh := he
    rw [heq] at hh
    linarith only [hu,hh]
  have hrpos : 0 < r := by linarith
  have hrTD : r < TD := by unfold TD; linarith
  have hden (a : ℝ) (ha : 0 ≤ a) (haT : a < TD) :
      0 < 6*TB*(3-4*a)*(TB-a) := by
    have hT := CourierResearch.TB_bounds
    have h1 : 0 < TB := by linarith [hT.1]
    have h2 : 0 < 3-4*a := by unfold TD at haT; linarith
    have h3 : 0 < TB-a := by unfold TD at haT; linarith [hT.1]
    positivity
  have hm := CourierResearch.poly_increasing CB hCB
  refine ⟨r,hrpos,hrTD,hrlo,hrhi,?_,?_,?_⟩
  · rw [CourierResearch.fA_eq CB r hrpos.le hrTD,he,zero_div]
  · intro a ha har
    have haTD := har.trans hrTD
    rw [CourierResearch.fA_eq CB a ha.le haTD]
    apply div_neg_of_neg_of_pos _ (hden a ha.le haTD)
    have hh := hm ⟨ha.le,haTD.le⟩ ⟨hrpos.le,hrTD.le⟩ har
    simpa only [he] using hh
  · intro a hra haTD
    have hapos := hrpos.trans hra
    rw [CourierResearch.fA_eq CB a hapos.le haTD]
    apply div_pos _ (hden a hapos.le haTD)
    have hh := hm ⟨hrpos.le,hrTD.le⟩ ⟨hapos.le,haTD.le⟩ hra
    simpa only [he] using hh

#print axioms solution
