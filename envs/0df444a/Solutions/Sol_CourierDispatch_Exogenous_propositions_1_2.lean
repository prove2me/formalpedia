-- Prove2me | solution 1 for CourierDispatch.Exogenous.propositions_1_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:30:36.562982+00:00
-- url     : https://prove2.me/submissions/b360cf71-fb45-484b-93df-4180182d9c81

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
theorem CourierResearch.unique_root (CB : ℝ) (hCB : CBRange CB) :
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




open CourierDispatch.Exogenous

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mingliu Chen and Ming Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063.
theorem CourierResearch.wait_difference (CB r lam : ℝ) (hr : 0 < r) (hlam : 0 < lam) (hstab : lam*r < TD) :
    WD lam (muD r) CD-WB r lam (muB r) CB = fA CB (lam*r)/lam := by
  have hp := Real.pi_pos
  have hdb : 32+15*Real.pi ≠ 0 := by positivity
  have hmuD : muD r = TD/r := by unfold muD TD; ring
  have hmuB : muB r = TB/(2*r) := by
    unfold muB TB
    field_simp
    ring
  have hTB : TD < TB := by
    unfold TD TB
    apply (lt_div_iff₀ (by positivity : 0 < 2*(32+15*Real.pi))).2
    linarith [Real.pi_gt_three]
  have hTD : TD ≠ 0 := by norm_num [TD]
  have hTB0 : TB ≠ 0 := by
    have hTDpos : 0 < TD := by norm_num [TD]
    exact (hTDpos.trans hTB).ne'
  have hd : TD-r*lam ≠ 0 := by nlinarith only [hstab]
  have hb : TB-r*lam ≠ 0 := by nlinarith only [hstab,hTB]
  rw [hmuD,hmuB]
  unfold WD WB fA
  field_simp [hr.ne',hlam.ne',hTD,hTB0,hd,hb]
  ring



-- Full waiting-time and revenue comparisons in Propositions 1 and 2.
theorem solution (CB : ℝ) (hCB : CBRange CB) :
    ∃ a₁ : ℝ, 0 < a₁ ∧ a₁ < TD ∧
      ∀ r lam : ℝ, 0 < r → 0 < lam → lam*r < TD →
        (WD lam (muD r) CD < WB r lam (muB r) CB ↔ lam*r < a₁) ∧
        (WB r lam (muB r) CB < WD lam (muD r) CD ↔ a₁ < lam*r) ∧
        (∀ (Q : ℝ → ℝ) (Lam c : ℝ), 0 < Lam → lam ≤ Lam*r^2 → 0 < c →
          (V Q Lam r c lam (WB r lam (muB r) CB) < V Q Lam r c lam (WD lam (muD r) CD) ↔
            lam*r < a₁) ∧
          (V Q Lam r c lam (WD lam (muD r) CD) < V Q Lam r c lam (WB r lam (muB r) CB) ↔
            a₁ < lam*r)) := by
  obtain ⟨a,ha,haT,_,_,hz,hneg,hpos⟩ := CourierResearch.unique_root CB hCB
  have hn (x : ℝ) (hx : 0 < x) (hxT : x < TD) : fA CB x < 0 ↔ x < a := by
    constructor
    · intro hf
      rcases lt_trichotomy x a with h | h | h
      · exact h
      · rw [h,hz] at hf; exact (lt_irrefl _ hf).elim
      · have hh := hpos x h hxT; linarith only [hf,hh]
    · exact hneg x hx
  have hp (x : ℝ) (hx : 0 < x) (hxT : x < TD) : 0 < fA CB x ↔ a < x := by
    constructor
    · intro hf
      rcases lt_trichotomy x a with h | h | h
      · have hh := hneg x hx h; linarith only [hf,hh]
      · rw [h,hz] at hf; exact (lt_irrefl _ hf).elim
      · exact h
    · exact fun h => hpos x h hxT
  refine ⟨a,ha,haT,?_⟩
  intro r lam hr hlam hstab
  have hdiff := CourierResearch.wait_difference CB r lam hr hlam hstab
  have h1 : WD lam (muD r) CD < WB r lam (muB r) CB ↔ lam*r<a := by
    rw [← sub_neg,hdiff,div_lt_iff₀ hlam,zero_mul]
    exact hn (lam*r) (mul_pos hlam hr) hstab
  have h2 : WB r lam (muB r) CB < WD lam (muD r) CD ↔ a<lam*r := by
    rw [← sub_pos,hdiff,lt_div_iff₀ hlam,zero_mul]
    exact hp (lam*r) (mul_pos hlam hr) hstab
  refine ⟨h1,h2,?_⟩
  intro Q Lam c _ _ hc
  have hrev (x y : ℝ) : V Q Lam r c lam x < V Q Lam r c lam y ↔ y < x := by
    unfold V
    rw [mul_lt_mul_iff_right₀ hlam,sub_lt_sub_iff_left,mul_lt_mul_iff_right₀ hc]
  exact ⟨(hrev _ _).trans h1,(hrev _ _).trans h2⟩

#print axioms solution
