-- Prove2me | solution 1 for ConfoundPromo.LongRun.optimal_signal
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T08:56:11.668974+00:00
-- url     : https://prove2.me/submissions/8bb0773d-65c3-40b6-8e85-0d6702122144

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

open ConfoundPromo.LongRun
open Finset

namespace CPSolOS

lemma bayes_same (μ l : ℝ) : bayes μ l l = μ := by
  unfold bayes
  have : μ * l + (1 - μ) * l = l := by ring
  rw [this]
  split_ifs with h
  · rfl
  · field_simp

/-- The single-price one-period rule promoting only at price `w.1`, with probabilities
`w.2.1` (state `φ_H`) and `w.2.2` (state `φ_L`). -/
noncomputable def rule (w : ℝ × ℝ × ℝ) : ℝ → Bool → ℝ :=
  fun q b => if q = w.1 then (if b then w.2.1 else w.2.2) else 0

/-- A feasible confounding myopic one-period choice at belief `μ`. -/
def Feas (M : Market) (μ : ℝ) (w : ℝ × ℝ × ℝ) : Prop :=
  IsValidRule (rule w) ∧ IsMyopicChoice M μ (rule w) w.1 ∧ IsConfoundingChoice M μ (rule w) w.1

/-- current expected surplus at price `p` with promotion probabilities `aH, aL`. -/
def SSf (M : Market) (μ p aH aL : ℝ) : ℝ :=
  μ * surplus M true aH p + (1 - μ) * surplus M false aL p

/-- current expected revenue at price `p` with promotion probabilities `aH, aL`. -/
def revf (M : Market) (μ p aH aL : ℝ) : ℝ :=
  p * (μ * saleProb M true aH p + (1 - μ) * saleProb M false aL p)

/-- confounding defect. -/
def conff (M : Market) (μ p aH aL : ℝ) : ℝ :=
  μ * (1 - μ) * (saleProb M true aH p - saleProb M false aL p)

/-- probability of a patient-only consumer: `1 - φ̄(μ)`. -/
def cc (M : Market) (μ : ℝ) : ℝ := μ * (1 - M.phiH) + (1 - μ) * (1 - M.phiL)

lemma expSurplus_rule (M : Market) (μ p aH aL : ℝ) :
    expSurplus M μ (rule (p, aH, aL)) p = SSf M μ p aH aL := by
  simp [expSurplus, rule, SSf]

lemma expRev_rule (M : Market) (μ p aH aL : ℝ) :
    expRev M μ (rule (p, aH, aL)) p = revf M μ p aH aL := by
  simp [expRev, rule, revf]

lemma expRev_rule_ne (M : Market) (μ p aH aL q : ℝ) (hq : q ≠ p) :
    expRev M μ (rule (p, aH, aL)) q = cc M μ * (q * M.rhoC q) := by
  simp [expRev, rule, hq, cc, saleProb, Market.phiVal]
  ring

lemma expSurplus_rule_ne (M : Market) (μ p aH aL q : ℝ) (hq : q ≠ p) :
    expSurplus M μ (rule (p, aH, aL)) q = SSf M μ q 0 0 := by
  simp [expSurplus, rule, hq, SSf]

lemma cc_pos (M : Market) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    0 < cc M μ := by
  have := hM.phiH_lt_one
  have := hM.phiL_lt_phiH
  obtain ⟨h0, h1⟩ := hμ
  unfold cc
  nlinarith

lemma saleProb_nonneg (M : Market) (hM : M.Standing) (b : Bool) (a p : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ M.price) : 0 ≤ saleProb M b a p := by
  have hφL := hM.phiL_pos
  have hφLH := hM.phiL_lt_phiH
  have hφH := hM.phiH_lt_one
  have hc := hM.rhoC_nonneg p hp
  have h0 := le_trans hc (hM.rhoC_le_rho0 p hp)
  obtain ⟨ha0, _⟩ := ha
  unfold saleProb Market.phiVal
  cases b
  · simp only [Bool.false_eq_true, if_false]
    exact add_nonneg (mul_nonneg (mul_nonneg hφL.le ha0) h0) (mul_nonneg (by linarith) hc)
  · simp only [if_true]
    exact add_nonneg (mul_nonneg (mul_nonneg (by linarith) ha0) h0) (mul_nonneg (by linarith) hc)

/-- The patient-revenue maximizer `p*`. -/
lemma exists_pstar (M : Market) (hM : M.Standing) :
    ∃ ps ∈ M.price, 0 ≤ ps ∧ (∀ q ∈ M.price, q * M.rhoC q ≤ ps * M.rhoC ps) ∧
      (∀ q ∈ M.price, q ≠ ps → q * M.rhoC q < ps * M.rhoC ps) := by
  set P := M.price with hP
  have hPne : P.Nonempty := ⟨0, hM.pLo_nonpos, hM.pHi_nonneg⟩
  have hPc : IsCompact P := isCompact_Icc
  have hcontc : ContinuousOn M.rhoC P := by
    obtain ⟨K, hK⟩ := hM.rhoC_lipschitz; exact hK.continuousOn
  have hRc : ContinuousOn (fun q => q * M.rhoC q) P := continuousOn_id.mul hcontc
  obtain ⟨ps, hps, hmax⟩ := hPc.exists_isMaxOn hPne hRc
  have hmax' : ∀ q ∈ P, q * M.rhoC q ≤ ps * M.rhoC ps := fun q hq => hmax hq
  have hstrict : ∀ q ∈ P, q ≠ ps → q * M.rhoC q < ps * M.rhoC ps := by
    intro q hq hne
    have hc := hM.revC_strictConcave.2 hq hps hne (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    have hm : (1/2 : ℝ) • q + (1/2 : ℝ) • ps ∈ P :=
      (convex_Icc M.pLo M.pHi) hq hps (by norm_num) (by norm_num) (by norm_num)
    have hRm := hmax' _ hm
    simp only [smul_eq_mul] at hc hRm
    linarith
  refine ⟨ps, hps, ?_, hmax', hstrict⟩
  by_contra hneg
  push_neg at hneg
  have h0P : (0:ℝ) ∈ P := ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩
  have hc := hM.rhoC_nonneg ps hps
  have h1 : ps * M.rhoC ps ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg.le hc
  have h2 := hstrict 0 h0P (ne_of_gt hneg)
  simp at h2
  linarith

section Fixed

variable (M : Market) (hM : M.Standing) (ps : ℝ) (hps : ps ∈ M.price) (hps0 : 0 ≤ ps)
  (hmax : ∀ q ∈ M.price, q * M.rhoC q ≤ ps * M.rhoC ps)
  (hstrict : ∀ q ∈ M.price, q ≠ ps → q * M.rhoC q < ps * M.rhoC ps)

/-- The closed constraint set at belief `μ`: valid probabilities, price in `P`, revenue at least
`(1 - φ̄(μ)) p* ρ̄c(p*)`, and equal sale probabilities when `μ ∈ (0,1)`. -/
def InGr (μ p aH aL : ℝ) : Prop :=
  μ ∈ Set.Icc (0 : ℝ) 1 ∧ p ∈ M.price ∧ aH ∈ Set.Icc (0 : ℝ) 1 ∧ aL ∈ Set.Icc (0 : ℝ) 1 ∧
    cc M μ * (ps * M.rhoC ps) ≤ revf M μ p aH aL ∧ conff M μ p aH aL = 0

include hM hps hps0 in
/-- Every feasible confounding myopic choice lies in the closed constraint set. -/
lemma feas_to_gr (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (a : ℝ → Bool → ℝ) (p : ℝ)
    (ha : IsValidRule a) (hmy : IsMyopicChoice M μ a p) (hcf : IsConfoundingChoice M μ a p) :
    InGr M ps μ p (a p true) (a p false) ∧
      expSurplus M μ a p = SSf M μ p (a p true) (a p false) := by
  obtain ⟨hp, hrev, _⟩ := hmy
  refine ⟨⟨hμ, hp, ha p true, ha p false, ?_, ?_⟩, rfl⟩
  · have h1 := hrev ps hps
    have e1 : expRev M μ a p = revf M μ p (a p true) (a p false) := rfl
    rw [← e1]
    refine le_trans ?_ h1
    have hφL := hM.phiL_pos
    have hφLH := hM.phiL_lt_phiH
    have hφH := hM.phiH_lt_one
    have hc := hM.rhoC_nonneg ps hps
    have h0 := le_trans hc (hM.rhoC_le_rho0 ps hps)
    obtain ⟨hμ0, hμ1⟩ := hμ
    obtain ⟨a1, _⟩ := ha ps true
    obtain ⟨a2, _⟩ := ha ps false
    simp only [expRev, cc, saleProb, Market.phiVal, if_true, Bool.false_eq_true, if_false]
    have : 0 ≤ ps * M.rho0 ps * (μ * M.phiH * a ps true + (1 - μ) * M.phiL * a ps false) := by
      apply mul_nonneg (mul_nonneg hps0 h0)
      have : 0 ≤ 1 - μ := by linarith
      exact add_nonneg (mul_nonneg (mul_nonneg hμ0 (by linarith)) a1)
        (mul_nonneg (mul_nonneg this hφL.le) a2)
    nlinarith
  · have h := hcf true
    have hH := saleProb_nonneg M hM true (a p true) p (ha p true) hp
    have hL := saleProb_nonneg M hM false (a p false) p (ha p false) hp
    simp only [likelihood, if_true] at h
    unfold bayes at h
    unfold conff
    obtain ⟨hμ0, hμ1⟩ := hμ
    split_ifs at h with hden
    · have h1 : 0 ≤ μ * saleProb M true (a p true) p := mul_nonneg hμ0 hH
      have h2 : 0 ≤ (1 - μ) * saleProb M false (a p false) p := mul_nonneg (by linarith) hL
      have e1 : μ * saleProb M true (a p true) p = 0 := by linarith
      have e2 : (1 - μ) * saleProb M false (a p false) p = 0 := by linarith
      calc μ * (1 - μ) * (saleProb M true (a p true) p - saleProb M false (a p false) p)
          = (1 - μ) * (μ * saleProb M true (a p true) p) -
              μ * ((1 - μ) * saleProb M false (a p false) p) := by ring
        _ = 0 := by rw [e1, e2]; ring
    · rw [div_eq_iff hden] at h
      linear_combination h

include hM hmax hstrict in
/-- A point of the constraint set whose surplus is at least that of `p*` without promotion is a
feasible confounding myopic choice. -/
lemma gr_to_feas (μ p aH aL : ℝ) (hg : InGr M ps μ p aH aL)
    (hS0 : SSf M μ ps 0 0 ≤ SSf M μ p aH aL) : Feas M μ (p, aH, aL) := by
  obtain ⟨hμ, hp, haH, haL, hrev, hconf⟩ := hg
  have hcpos := cc_pos M hM μ hμ
  refine ⟨?_, ⟨hp, ?_, ?_⟩, ?_⟩
  · intro q b
    simp only [rule]
    split_ifs
    · exact haH
    · exact haL
    · exact ⟨le_refl _, zero_le_one⟩
  · intro q hq
    by_cases hqp : q = p
    · rw [hqp]
    · rw [expRev_rule_ne M μ p aH aL q hqp, expRev_rule]
      have := hmax q hq
      nlinarith
  · intro q hq heq
    by_cases hqp : q = p
    · rw [hqp]
    · rw [expRev_rule_ne M μ p aH aL q hqp, expRev_rule] at heq
      have h1 := hmax q hq
      have hqs : q = ps := by
        by_contra hne
        have h2 := hstrict q hq hne
        nlinarith
      rw [expSurplus_rule_ne M μ p aH aL q hqp, expSurplus_rule, hqs]
      exact hS0
  · intro y
    obtain ⟨hμ0, hμ1⟩ := hμ
    simp only [rule, if_true, Bool.false_eq_true, if_false]
    unfold conff at hconf
    rcases eq_or_lt_of_le hμ0 with h0 | h0
    · subst h0
      unfold bayes
      split_ifs <;> simp
    rcases eq_or_lt_of_le hμ1 with h1 | h1
    · subst h1
      unfold bayes
      split_ifs with hd
      · rfl
      · have e : (1:ℝ) * likelihood M true aH p y + (1 - 1) * likelihood M false aL p y =
            1 * likelihood M true aH p y := by ring
        rw [e] at hd ⊢
        exact div_self hd
    · have hne : μ * (1 - μ) ≠ 0 := by
        apply mul_ne_zero h0.ne' ; linarith
      have hs : saleProb M true aH p = saleProb M false aL p := by
        have := (mul_eq_zero.mp hconf).resolve_left hne
        linarith
      have hl : likelihood M true aH p y = likelihood M false aL p y := by
        simp only [likelihood, hs]
      rw [hl]
      exact bayes_same _ _

end Fixed

/-- Proposition 3, one-period form: at every belief there is a feasible confounding myopic
single-price choice (the construction of the proof of Proposition 3). -/
lemma exists_feas (M : Market) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ w, Feas M μ w := by
  set P := M.price with hP
  have hφL := hM.phiL_pos
  have hφLH := hM.phiL_lt_phiH
  have hφH := hM.phiH_lt_one
  set R : ℝ → ℝ := fun q => q * (M.phiL * M.rho0 q + (1 - M.phiL) * M.rhoC q) with hR
  have hPne : P.Nonempty := ⟨0, hM.pLo_nonpos, hM.pHi_nonneg⟩
  have hPc : IsCompact P := isCompact_Icc
  have hcont0 : ContinuousOn M.rho0 P := by
    obtain ⟨K, hK⟩ := hM.rho0_lipschitz; exact hK.continuousOn
  have hcontc : ContinuousOn M.rhoC P := by
    obtain ⟨K, hK⟩ := hM.rhoC_lipschitz; exact hK.continuousOn
  have hRc : ContinuousOn R P := by
    apply ContinuousOn.mul continuousOn_id
    exact (continuousOn_const.mul hcont0).add (continuousOn_const.mul hcontc)
  obtain ⟨ps, hps, hmax⟩ := hPc.exists_isMaxOn hPne hRc
  have hstrict : ∀ q ∈ P, q ≠ ps → R q < R ps := by
    intro q hq hne
    have h0 := hM.rev0_strictConcave.2 hq hps hne (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    have hc := hM.revC_strictConcave.2 hq hps hne (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    have hm : (1/2 : ℝ) • q + (1/2 : ℝ) • ps ∈ P :=
      (convex_Icc M.pLo M.pHi) hq hps (by norm_num) (by norm_num) (by norm_num)
    have hRm : R ((1/2 : ℝ) • q + (1/2 : ℝ) • ps) ≤ R ps := hmax hm
    simp only [smul_eq_mul] at h0 hc hRm
    simp only [hR] at hRm ⊢
    have e1 := mul_lt_mul_of_pos_left h0 hφL
    have e2 := mul_lt_mul_of_pos_left hc (by linarith : (0:ℝ) < 1 - M.phiL)
    linear_combination (2:ℝ) * e1 + 2 * e2 + 2 * hRm
  have hneg : ∀ q ∈ P, q < 0 → 0 < M.rhoC q := by
    intro q hq hq0
    by_contra hcon
    have hz : M.rhoC q = 0 := le_antisymm (not_lt.mp hcon) (hM.rhoC_nonneg q hq)
    have h0P : (0:ℝ) ∈ P := ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩
    have hs := hM.revC_strictConcave.2 hq h0P (ne_of_lt hq0) (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    have hm : (1/2 : ℝ) • q + (1/2 : ℝ) • (0:ℝ) ∈ P :=
      (convex_Icc M.pLo M.pHi) hq h0P (by norm_num) (by norm_num) (by norm_num)
    have hnn := hM.rhoC_nonneg _ hm
    simp only [smul_eq_mul, hz, mul_zero, zero_mul, add_zero] at hs hnn
    nlinarith
  set aH : ℝ := (M.phiL * M.rho0 ps + (M.phiH - M.phiL) * M.rhoC ps) / (M.phiH * M.rho0 ps)
    with haH
  have hc0 := hM.rhoC_nonneg ps hps
  have hcle := hM.rhoC_le_rho0 ps hps
  have haH0 : 0 ≤ aH := by
    apply div_nonneg
    · nlinarith
    · nlinarith
  have haH1 : aH ≤ 1 := by
    apply div_le_one_of_le₀
    · nlinarith
    · nlinarith
  have hsale : saleProb M true aH ps = saleProb M false 1 ps := by
    simp only [saleProb, Market.phiVal, if_true, Bool.false_eq_true, if_false]
    rcases eq_or_lt_of_le (le_trans hc0 hcle) with h0 | h0
    · have hc' : M.rhoC ps = 0 := le_antisymm (h0 ▸ hcle) hc0
      rw [← h0, hc']; ring
    · rw [haH]
      have : M.phiH ≠ 0 := by linarith
      have : M.rho0 ps ≠ 0 := h0.ne'
      field_simp
      ring
  refine ⟨(ps, aH, 1), ?_, ⟨hps, ?_, ?_⟩, ?_⟩
  · intro q b
    simp only [rule]
    split_ifs
    · exact ⟨haH0, haH1⟩
    · exact ⟨zero_le_one, le_refl _⟩
    · exact ⟨le_refl _, zero_le_one⟩
  · have hrevp : expRev M μ (rule (ps, aH, 1)) ps = R ps := by
      rw [expRev_rule]
      simp only [revf, hR]
      rw [hsale]
      simp only [saleProb, Market.phiVal, Bool.false_eq_true, if_false]
      ring
    intro q hq
    by_cases hqe : q = ps
    · rw [hqe]
    · rw [hrevp, expRev_rule_ne M μ ps aH 1 q hqe]
      obtain ⟨h0, h1⟩ := hμ
      unfold cc
      rcases le_or_gt 0 q with hq0 | hq0
      · have hcq := hM.rhoC_nonneg q hq
        have h0q := hM.rhoC_le_rho0 q hq
        have hRq := hstrict q hq hqe
        simp only [hR] at hRq
        have hcoef : μ * (1 - M.phiH) + (1 - μ) * (1 - M.phiL) ≤ 1 - M.phiL := by nlinarith
        have e1 : (μ * (1 - M.phiH) + (1 - μ) * (1 - M.phiL)) * (q * M.rhoC q) ≤
            (1 - M.phiL) * (q * M.rhoC q) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg hq0 hcq)
        have e2 : (1 - M.phiL) * (q * M.rhoC q) ≤
            q * (M.phiL * M.rho0 q + (1 - M.phiL) * M.rhoC q) := by
          have : 0 ≤ q * (M.phiL * M.rho0 q) :=
            mul_nonneg hq0 (mul_nonneg hφL.le (le_trans hcq h0q))
          nlinarith
        linarith
      · have hcq := hneg q hq hq0
        have hcoef : 0 < μ * (1 - M.phiH) + (1 - μ) * (1 - M.phiL) := by nlinarith
        have h0P : (0:ℝ) ∈ P := ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩
        have hR0 : R 0 ≤ R ps := hmax h0P
        simp only [hR, zero_mul] at hR0
        simp only [hR]
        have : (μ * (1 - M.phiH) + (1 - μ) * (1 - M.phiL)) * (q * M.rhoC q) < 0 :=
          mul_neg_of_pos_of_neg hcoef (mul_neg_of_neg_of_pos hq0 hcq)
        linarith
  · have hrevp : expRev M μ (rule (ps, aH, 1)) ps = R ps := by
      rw [expRev_rule]
      simp only [revf, hR]
      rw [hsale]
      simp only [saleProb, Market.phiVal, Bool.false_eq_true, if_false]
      ring
    intro q hq heq
    by_cases hqe : q = ps
    · rw [hqe]
    · exfalso
      rw [hrevp, expRev_rule_ne M μ ps aH 1 q hqe] at heq
      obtain ⟨h0, h1⟩ := hμ
      unfold cc at heq
      rcases le_or_gt 0 q with hq0 | hq0
      · have hcq := hM.rhoC_nonneg q hq
        have h0q := hM.rhoC_le_rho0 q hq
        have hRq := hstrict q hq hqe
        simp only [hR] at hRq
        have hcoef : μ * (1 - M.phiH) + (1 - μ) * (1 - M.phiL) ≤ 1 - M.phiL := by nlinarith
        have e1 : (μ * (1 - M.phiH) + (1 - μ) * (1 - M.phiL)) * (q * M.rhoC q) ≤
            (1 - M.phiL) * (q * M.rhoC q) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg hq0 hcq)
        have e2 : (1 - M.phiL) * (q * M.rhoC q) ≤
            q * (M.phiL * M.rho0 q + (1 - M.phiL) * M.rhoC q) := by
          have : 0 ≤ q * (M.phiL * M.rho0 q) :=
            mul_nonneg hq0 (mul_nonneg hφL.le (le_trans hcq h0q))
          nlinarith
        simp only [hR] at heq
        linarith
      · have hcq := hneg q hq hq0
        have hcoef : 0 < μ * (1 - M.phiH) + (1 - μ) * (1 - M.phiL) := by nlinarith
        have h0P : (0:ℝ) ∈ P := ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩
        have hR0 : R 0 ≤ R ps := hmax h0P
        simp only [hR, zero_mul] at hR0
        simp only [hR] at heq
        have : (μ * (1 - M.phiH) + (1 - μ) * (1 - M.phiL)) * (q * M.rhoC q) < 0 :=
          mul_neg_of_pos_of_neg hcoef (mul_neg_of_neg_of_pos hq0 hcq)
        linarith
  · intro y
    simp only [rule, if_true, Bool.false_eq_true, if_false]
    have hl : likelihood M true aH ps y = likelihood M false 1 ps y := by
      simp only [likelihood, hsale]
    rw [hl]
    exact bayes_same _ _

/-! ## Continuity and compactness -/

/-- clamp to the price interval -/
def cl (M : Market) (p : ℝ) : ℝ := max M.pLo (min M.pHi p)

lemma cl_mem (M : Market) (hM : M.Standing) (p : ℝ) : cl M p ∈ M.price := by
  have : M.pLo ≤ M.pHi := le_trans hM.pLo_nonpos hM.pHi_nonneg
  exact ⟨le_max_left _ _, max_le this (min_le_left _ _)⟩

lemma cl_eq (M : Market) (p : ℝ) (hp : p ∈ M.price) : cl M p = p := by
  unfold cl
  rw [min_eq_right hp.2, max_eq_right hp.1]

lemma cl_cont (M : Market) : Continuous (cl M) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma comp_cont (M : Market) (hM : M.Standing) (f : ℝ → ℝ)
    (hf : ∃ K, LipschitzOnWith K f M.price) : Continuous (fun p => f (cl M p)) := by
  obtain ⟨K, hK⟩ := hf
  exact hK.continuousOn.comp_continuous (cl_cont M) (cl_mem M hM)

/-- generic shape of the clamped surplus -/
def Gshape (φH φL Wout : ℝ) (f g : ℝ → ℝ) (w : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  w.1 * (φH * (Wout + w.2.2.1 * (f w.2.1 - Wout)) + (1 - φH) * g w.2.1) +
    (1 - w.1) * (φL * (Wout + w.2.2.2 * (f w.2.1 - Wout)) + (1 - φL) * g w.2.1)

lemma Gshape_cont (φH φL Wout : ℝ) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (Gshape φH φL Wout f g) := by
  unfold Gshape
  fun_prop

/-- generic shape of the clamped revenue -/
def Rshape (φH φL : ℝ) (c f g : ℝ → ℝ) (w : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  c w.2.1 * (w.1 * (φH * w.2.2.1 * f w.2.1 + (1 - φH) * g w.2.1) +
    (1 - w.1) * (φL * w.2.2.2 * f w.2.1 + (1 - φL) * g w.2.1))

lemma Rshape_cont (φH φL : ℝ) (c f g : ℝ → ℝ) (hc : Continuous c) (hf : Continuous f)
    (hg : Continuous g) : Continuous (Rshape φH φL c f g) := by
  unfold Rshape
  fun_prop

/-- generic shape of the clamped confounding defect -/
def Cshape (φH φL : ℝ) (f g : ℝ → ℝ) (w : ℝ × ℝ × ℝ × ℝ) : ℝ :=
  w.1 * (1 - w.1) * ((φH * w.2.2.1 * f w.2.1 + (1 - φH) * g w.2.1) -
    (φL * w.2.2.2 * f w.2.1 + (1 - φL) * g w.2.1))

lemma Cshape_cont (φH φL : ℝ) (f g : ℝ → ℝ) (hf : Continuous f)
    (hg : Continuous g) : Continuous (Cshape φH φL f g) := by
  unfold Cshape
  fun_prop

/-- clamped surplus -/
def Gf (M : Market) : ℝ × ℝ × ℝ × ℝ → ℝ :=
  Gshape M.phiH M.phiL M.Wout (fun p => M.W0 (cl M p)) (fun p => M.Wc (cl M p))

/-- clamped revenue -/
def Rf (M : Market) : ℝ × ℝ × ℝ × ℝ → ℝ :=
  Rshape M.phiH M.phiL (cl M) (fun p => M.rho0 (cl M p)) (fun p => M.rhoC (cl M p))

/-- clamped confounding defect -/
def Cf (M : Market) : ℝ × ℝ × ℝ × ℝ → ℝ :=
  Cshape M.phiH M.phiL (fun p => M.rho0 (cl M p)) (fun p => M.rhoC (cl M p))

lemma Gf_cont (M : Market) (hM : M.Standing) : Continuous (Gf M) :=
  Gshape_cont _ _ _ _ _ (comp_cont M hM _ hM.W0_lipschitz) (comp_cont M hM _ hM.Wc_lipschitz)

lemma Rf_cont (M : Market) (hM : M.Standing) : Continuous (Rf M) :=
  Rshape_cont _ _ _ _ _ (cl_cont M) (comp_cont M hM _ hM.rho0_lipschitz)
    (comp_cont M hM _ hM.rhoC_lipschitz)

lemma Cf_cont (M : Market) (hM : M.Standing) : Continuous (Cf M) :=
  Cshape_cont _ _ _ _ (comp_cont M hM _ hM.rho0_lipschitz) (comp_cont M hM _ hM.rhoC_lipschitz)

lemma Gf_eq (M : Market) (μ p aH aL : ℝ) (hp : p ∈ M.price) :
    Gf M (μ, p, aH, aL) = SSf M μ p aH aL := by
  simp only [Gf, Gshape, SSf, surplus, Market.phiVal, if_true, Bool.false_eq_true, if_false,
    cl_eq M p hp]

lemma Rf_eq (M : Market) (μ p aH aL : ℝ) (hp : p ∈ M.price) :
    Rf M (μ, p, aH, aL) = revf M μ p aH aL := by
  simp only [Rf, Rshape, revf, saleProb, Market.phiVal, if_true, Bool.false_eq_true, if_false,
    cl_eq M p hp]

lemma Cf_eq (M : Market) (μ p aH aL : ℝ) (hp : p ∈ M.price) :
    Cf M (μ, p, aH, aL) = conff M μ p aH aL := by
  simp only [Cf, Cshape, conff, saleProb, Market.phiVal, if_true, Bool.false_eq_true, if_false,
    cl_eq M p hp]

lemma cc_cont (M : Market) : Continuous (fun w : ℝ × ℝ × ℝ × ℝ => cc M w.1) := by
  unfold cc; fun_prop

/-- the box of beliefs, prices and promotion probabilities -/
def Bx (M : Market) : Set (ℝ × ℝ × ℝ × ℝ) :=
  Set.Icc (0:ℝ) 1 ×ˢ (M.price ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1))

lemma Bx_compact (M : Market) : IsCompact (Bx M) :=
  isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

/-- the graph of the closed constraint correspondence -/
def GrS (M : Market) (ps : ℝ) : Set (ℝ × ℝ × ℝ × ℝ) :=
  (Bx M ∩ {w | cc M w.1 * (ps * M.rhoC ps) ≤ Rf M w}) ∩ {w | Cf M w = 0}

lemma GrS_compact (M : Market) (hM : M.Standing) (ps : ℝ) : IsCompact (GrS M ps) :=
  ((Bx_compact M).inter_right (isClosed_le ((cc_cont M).mul continuous_const) (Rf_cont M hM))).inter_right
    (isClosed_eq (Cf_cont M hM) continuous_const)

lemma mem_GrS (M : Market) (ps μ p aH aL : ℝ) :
    (μ, p, aH, aL) ∈ GrS M ps ↔ InGr M ps μ p aH aL := by
  constructor
  · rintro ⟨⟨⟨hμ, hp, haH, haL⟩, hr⟩, hc⟩
    simp only [Set.mem_setOf_eq] at hr hc
    rw [Rf_eq M μ p aH aL hp] at hr
    rw [Cf_eq M μ p aH aL hp] at hc
    exact ⟨hμ, hp, haH, haL, hr, hc⟩
  · rintro ⟨hμ, hp, haH, haL, hr, hc⟩
    refine ⟨⟨⟨hμ, hp, haH, haL⟩, ?_⟩, ?_⟩
    · show cc M μ * (ps * M.rhoC ps) ≤ Rf M (μ, p, aH, aL)
      rw [Rf_eq M μ p aH aL hp]; exact hr
    · show Cf M (μ, p, aH, aL) = 0
      rw [Cf_eq M μ p aH aL hp]; exact hc

lemma exists_bound (M : Market) (hM : M.Standing) :
    ∃ B, ∀ μ p aH aL, μ ∈ Set.Icc (0:ℝ) 1 → p ∈ M.price → aH ∈ Set.Icc (0:ℝ) 1 →
      aL ∈ Set.Icc (0:ℝ) 1 → SSf M μ p aH aL ≤ B := by
  obtain ⟨C, hC⟩ := (Bx_compact M).exists_bound_of_continuousOn (Gf_cont M hM).continuousOn
  refine ⟨C, fun μ p aH aL hμ hp haH haL => ?_⟩
  have := hC (μ, p, aH, aL) ⟨hμ, hp, haH, haL⟩
  rw [Gf_eq M μ p aH aL hp, Real.norm_eq_abs] at this
  exact le_trans (le_abs_self _) this

/-! ## Bounds on `W^C` -/

lemma WC_bdd (M : Market) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1) :
    BddAbove {v | ∃ (a : ℝ → Bool → ℝ) (p : ℝ), IsValidRule a ∧ IsMyopicChoice M μ a p ∧
      IsConfoundingChoice M μ a p ∧ v = expSurplus M μ a p} := by
  obtain ⟨B, hB⟩ := exists_bound M hM
  refine ⟨B, ?_⟩
  rintro v ⟨a, p, ha, hmy, hcf, rfl⟩
  have hp := hmy.1
  show expSurplus M μ a p ≤ B
  exact hB μ p _ _ hμ hp (ha p true) (ha p false)

lemma le_WC (M : Market) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1)
    (w : ℝ × ℝ × ℝ) (hw : Feas M μ w) :
    expSurplus M μ (rule w) w.1 ≤ WC M μ := by
  obtain ⟨hv, hmy, hcf⟩ := hw
  exact le_csSup (WC_bdd M hM μ hμ) ⟨rule w, w.1, hv, hmy, hcf, rfl⟩

lemma WC_le (M : Market) (hM : M.Standing) (ps : ℝ) (hps : ps ∈ M.price) (hps0 : 0 ≤ ps)
    (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1) (L : ℝ)
    (h : ∀ p aH aL, InGr M ps μ p aH aL → SSf M μ p aH aL ≤ L) : WC M μ ≤ L := by
  obtain ⟨w, hv, hmy, hcf⟩ := exists_feas M hM μ hμ
  unfold WC
  refine csSup_le ⟨expSurplus M μ (rule w) w.1, rule w, w.1, hv, hmy, hcf, rfl⟩ ?_
  rintro v ⟨a, p, ha, hmy', hcf', rfl⟩
  obtain ⟨hg, he⟩ := feas_to_gr M hM ps hps hps0 μ hμ a p ha hmy' hcf'
  rw [he]
  exact h _ _ _ hg

/-! ## Attainment -/

/-- `w` is a feasible confounding myopic choice attaining `W^C(μ)`. -/
def Att (M : Market) (μ : ℝ) (w : ℝ × ℝ × ℝ) : Prop :=
  Feas M μ w ∧ expSurplus M μ (rule w) w.1 = WC M μ

lemma attain (M : Market) (hM : M.Standing) (ps : ℝ)
    (hmax : ∀ q ∈ M.price, q * M.rhoC q ≤ ps * M.rhoC ps)
    (hstrict : ∀ q ∈ M.price, q ≠ ps → q * M.rhoC q < ps * M.rhoC ps)
    (μ p aH aL : ℝ) (hg : InGr M ps μ p aH aL)
    (hS0 : SSf M μ ps 0 0 ≤ SSf M μ p aH aL) (hWC : WC M μ ≤ SSf M μ p aH aL) :
    Att M μ (p, aH, aL) := by
  have hF := gr_to_feas M hM ps hmax hstrict μ p aH aL hg hS0
  refine ⟨hF, ?_⟩
  have h1 := le_WC M hM μ hg.1 _ hF
  have e : expSurplus M μ (rule (p, aH, aL)) (p, aH, aL).1 = SSf M μ p aH aL :=
    expSurplus_rule M μ p aH aL
  rw [e] at h1 ⊢
  exact le_antisymm h1 hWC

lemma revf_pstar (M : Market) (μ ps : ℝ) :
    revf M μ ps 0 0 = cc M μ * (ps * M.rhoC ps) := by
  simp only [revf, saleProb, Market.phiVal, cc, if_true, Bool.false_eq_true, if_false]
  ring

lemma pstar_gr (M : Market) (ps : ℝ) (hps : ps ∈ M.price) (μ : ℝ)
    (hμ : μ ∈ Set.Icc (0:ℝ) 1) (hμe : μ * (1 - μ) = 0) : InGr M ps μ ps 0 0 := by
  refine ⟨hμ, hps, ⟨le_refl _, zero_le_one⟩, ⟨le_refl _, zero_le_one⟩,
    le_of_eq (revf_pstar M μ ps).symm, ?_⟩
  simp only [conff, hμe, zero_mul]

lemma endpoint_attain (M : Market) (hM : M.Standing) (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0:ℝ) 1)
    (hμe : μ0 * (1 - μ0) = 0) : ∃ w, Att M μ0 w := by
  obtain ⟨ps, hps, hps0, hmax, hstrict⟩ := exists_pstar M hM
  set Fb := GrS M ps ∩ {w | w.1 = μ0} with hFb
  have hFc : IsCompact Fb :=
    (GrS_compact M hM ps).inter_right (isClosed_eq continuous_fst continuous_const)
  have hne : (μ0, ps, (0:ℝ), (0:ℝ)) ∈ Fb :=
    ⟨(mem_GrS M ps μ0 ps 0 0).2 (pstar_gr M ps hps μ0 hμ0 hμe), rfl⟩
  obtain ⟨w, hw, hwmax⟩ := hFc.exists_isMaxOn ⟨_, hne⟩ (Gf_cont M hM).continuousOn
  obtain ⟨μ', p, aH, aL⟩ := w
  obtain ⟨hwg, hw1⟩ := hw
  simp only [Set.mem_ofPred_eq] at hw1
  subst hw1
  have hg := (mem_GrS M ps μ' p aH aL).1 hwg
  have hp := hg.2.1
  refine ⟨(p, aH, aL), attain M hM ps hmax hstrict μ' p aH aL hg ?_ ?_⟩
  · have := hwmax hne
    simp only [Set.mem_ofPred_eq] at this
    rw [Gf_eq M _ _ _ _ hps, Gf_eq M _ _ _ _ hp] at this
    exact this
  · apply WC_le M hM ps hps hps0 μ' hg.1
    intro p' aH' aL' hg'
    have hmem : (μ', p', aH', aL') ∈ Fb := ⟨(mem_GrS M ps _ _ _ _).2 hg', rfl⟩
    have := hwmax hmem
    simp only [Set.mem_ofPred_eq] at this
    rw [Gf_eq M _ _ _ _ hg'.2.1, Gf_eq M _ _ _ _ hp] at this
    exact this

/-! ## Concavification -/

lemma hull_le (f : ℝ → ℝ) (V k μ0 : ℝ) (hL : ∀ x ∈ Set.Icc (0:ℝ) 1, f x ≤ V + k * (x - μ0))
    (z : ℝ) (hz : (μ0, z) ∈ convexHull ℝ {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1}) :
    z ≤ V := by
  have hconv : Convex ℝ {x : ℝ × ℝ | x.2 ≤ V + k * (x.1 - μ0)} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hx hy ⊢
    have e1 := mul_le_mul_of_nonneg_left hx ha
    have e2 := mul_le_mul_of_nonneg_left hy hb
    have : a * (V + k * (x.1 - μ0)) + b * (V + k * (y.1 - μ0)) =
        V + k * (a * x.1 + b * y.1 - μ0) := by
      linear_combination (V - k * μ0) * hab
    linarith
  have hsub : {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1} ⊆
      {x : ℝ × ℝ | x.2 ≤ V + k * (x.1 - μ0)} := by
    intro x hx
    exact le_trans hx.2 (hL x.1 hx.1)
  have := convexHull_min hsub hconv hz
  simp only [Set.mem_ofPred_eq, sub_self, mul_zero, add_zero] at this
  exact this

lemma hull_le_zero (f : ℝ → ℝ) (z : ℝ)
    (hz : ((0:ℝ), z) ∈ convexHull ℝ {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1}) :
    z ≤ f 0 := by
  have hconv : Convex ℝ {x : ℝ × ℝ | 0 ≤ x.1 ∧ (x.1 = 0 → x.2 ≤ f 0)} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hx hy ⊢
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    refine ⟨add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0), fun h0 => ?_⟩
    have hax : a * x.1 = 0 := by nlinarith [mul_nonneg ha hx0, mul_nonneg hb hy0]
    have hby : b * y.1 = 0 := by nlinarith [mul_nonneg ha hx0, mul_nonneg hb hy0]
    have e1 : a * x.2 ≤ a * f 0 := by
      rcases eq_or_lt_of_le ha with h | h
      · rw [← h]; simp
      · exact mul_le_mul_of_nonneg_left (hx1 ((mul_eq_zero.mp hax).resolve_left h.ne')) ha
    have e2 : b * y.2 ≤ b * f 0 := by
      rcases eq_or_lt_of_le hb with h | h
      · rw [← h]; simp
      · exact mul_le_mul_of_nonneg_left (hy1 ((mul_eq_zero.mp hby).resolve_left h.ne')) hb
    have : a * f 0 + b * f 0 = f 0 := by rw [← add_mul, hab, one_mul]
    linarith
  have hsub : {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1} ⊆
      {x : ℝ × ℝ | 0 ≤ x.1 ∧ (x.1 = 0 → x.2 ≤ f 0)} := by
    intro x hx
    refine ⟨hx.1.1, fun h => ?_⟩
    have := hx.2
    rw [h] at this
    exact this
  have := convexHull_min hsub hconv hz
  exact this.2 rfl

lemma hull_le_one (f : ℝ → ℝ) (z : ℝ)
    (hz : ((1:ℝ), z) ∈ convexHull ℝ {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1}) :
    z ≤ f 1 := by
  have hconv : Convex ℝ {x : ℝ × ℝ | x.1 ≤ 1 ∧ (x.1 = 1 → x.2 ≤ f 1)} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hx hy ⊢
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨hy0, hy1⟩ := hy
    have hx0' : 0 ≤ 1 - x.1 := by linarith
    have hy0' : 0 ≤ 1 - y.1 := by linarith
    refine ⟨by nlinarith [mul_nonneg ha hx0', mul_nonneg hb hy0'], fun h0 => ?_⟩
    have hax : a * (1 - x.1) = 0 := by nlinarith [mul_nonneg ha hx0', mul_nonneg hb hy0']
    have hby : b * (1 - y.1) = 0 := by nlinarith [mul_nonneg ha hx0', mul_nonneg hb hy0']
    have e1 : a * x.2 ≤ a * f 1 := by
      rcases eq_or_lt_of_le ha with h | h
      · rw [← h]; simp
      · have := (mul_eq_zero.mp hax).resolve_left h.ne'
        exact mul_le_mul_of_nonneg_left (hx1 (by linarith)) ha
    have e2 : b * y.2 ≤ b * f 1 := by
      rcases eq_or_lt_of_le hb with h | h
      · rw [← h]; simp
      · have := (mul_eq_zero.mp hby).resolve_left h.ne'
        exact mul_le_mul_of_nonneg_left (hy1 (by linarith)) hb
    have : a * f 1 + b * f 1 = f 1 := by rw [← add_mul, hab, one_mul]
    linarith
  have hsub : {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1} ⊆
      {x : ℝ × ℝ | x.1 ≤ 1 ∧ (x.1 = 1 → x.2 ≤ f 1)} := by
    intro x hx
    refine ⟨hx.1.2, fun h => ?_⟩
    have := hx.2
    rw [h] at this
    exact this
  have := convexHull_min hsub hconv hz
  exact this.2 rfl

lemma co_eq_of (f : ℝ → ℝ) (μ0 V : ℝ)
    (hle : ∀ z, (μ0, z) ∈ convexHull ℝ {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1} →
      z ≤ V)
    (hmem : (μ0, V) ∈ convexHull ℝ {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1}) :
    co f μ0 = V := by
  unfold co
  exact le_antisymm (csSup_le ⟨V, hmem⟩ hle) (le_csSup ⟨V, hle⟩ hmem)

lemma co_endpoint (M : Market) (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0:ℝ) 1) (hμe : μ0 * (1 - μ0) = 0) :
    co (WC M) μ0 = WC M μ0 := by
  apply co_eq_of
  · intro z hz
    rcases mul_eq_zero.mp hμe with h | h
    · subst h; exact hull_le_zero _ z hz
    · have : μ0 = 1 := by linarith
      subst this; exact hull_le_one _ z hz
  · exact subset_convexHull ℝ _ ⟨hμ0, le_refl _⟩

/-! ## Interior priors: the optimal split -/

lemma interior_split (M : Market) (hM : M.Standing) (μ0 : ℝ) (h0 : 0 < μ0) (h1 : μ0 < 1) :
    ∃ (l x1 x2 : ℝ) (w1 w2 : ℝ × ℝ × ℝ), 0 ≤ l ∧ l ≤ 1 ∧ x1 ∈ Set.Icc (0:ℝ) 1 ∧
      x2 ∈ Set.Icc (0:ℝ) 1 ∧ l * x1 + (1 - l) * x2 = μ0 ∧ (0 < l → Att M x1 w1) ∧
      (0 < 1 - l → Att M x2 w2) ∧ co (WC M) μ0 = l * WC M x1 + (1 - l) * WC M x2 := by
  obtain ⟨ps, hps, hps0, hmax, hstrict⟩ := exists_pstar M hM
  set G := GrS M ps with hG
  set D : Set (ℝ × (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ × ℝ)) :=
    (Set.Icc (0:ℝ) 1 ×ˢ (G ×ˢ G)) ∩ {d | d.1 * d.2.1.1 + (1 - d.1) * d.2.2.1 = μ0} with hD
  have hDc : IsCompact D :=
    (isCompact_Icc.prod ((GrS_compact M hM ps).prod (GrS_compact M hM ps))).inter_right
      (isClosed_eq (by fun_prop) continuous_const)
  set F : ℝ × (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ × ℝ) → ℝ :=
    fun d => d.1 * Gf M d.2.1 + (1 - d.1) * Gf M d.2.2 with hF
  have hFc : Continuous F := by
    have key : ∀ g : (ℝ × ℝ × ℝ × ℝ) → ℝ, Continuous g →
        Continuous (fun d : ℝ × (ℝ × ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ × ℝ) =>
          d.1 * g d.2.1 + (1 - d.1) * g d.2.2) := by
      intro g hg; fun_prop
    exact key _ (Gf_cont M hM)
  have hw0 : ((0:ℝ), ps, (0:ℝ), (0:ℝ)) ∈ G :=
    (mem_GrS M ps 0 ps 0 0).2 (pstar_gr M ps hps 0 ⟨le_refl _, zero_le_one⟩ (by ring))
  have hw1 : ((1:ℝ), ps, (0:ℝ), (0:ℝ)) ∈ G :=
    (mem_GrS M ps 1 ps 0 0).2 (pstar_gr M ps hps 1 ⟨zero_le_one, le_refl _⟩ (by ring))
  have hDne : (1 - μ0, ((0:ℝ), ps, (0:ℝ), (0:ℝ)), ((1:ℝ), ps, (0:ℝ), (0:ℝ))) ∈ D :=
    ⟨⟨⟨by linarith, by linarith⟩, hw0, hw1⟩, by simp⟩
  obtain ⟨dst, hdst, hdmax⟩ := hDc.exists_isMaxOn ⟨_, hDne⟩ hFc.continuousOn
  obtain ⟨V, hV⟩ : ∃ V, V = F dst := ⟨_, rfl⟩
  have hFle : ∀ d ∈ D, F d ≤ V := fun d hd => hV ▸ hdmax hd
  -- the key two-point inequality
  have hK : ∀ v1 ∈ G, ∀ v2 ∈ G, v1.1 < μ0 → μ0 < v2.1 →
      (v2.1 - μ0) * Gf M v1 + (μ0 - v1.1) * Gf M v2 ≤ V * (v2.1 - v1.1) := by
    intro v1 hv1 v2 hv2 hlt hgt
    have ht : 0 < v2.1 - v1.1 := by linarith
    obtain ⟨lam, hlam⟩ : ∃ lam, lam = (v2.1 - μ0) / (v2.1 - v1.1) := ⟨_, rfl⟩
    have e1 : lam * (v2.1 - v1.1) = v2.1 - μ0 := by rw [hlam]; field_simp
    have e2 : (1 - lam) * (v2.1 - v1.1) = μ0 - v1.1 := by
      have : (1 - lam) * (v2.1 - v1.1) = (v2.1 - v1.1) - lam * (v2.1 - v1.1) := by ring
      rw [this, e1]; ring
    have hl0 : 0 ≤ lam := by rw [hlam]; exact div_nonneg (by linarith) ht.le
    have hl1 : lam ≤ 1 := by rw [hlam, div_le_one ht]; linarith
    have hmem : (lam, v1, v2) ∈ D := by
      refine ⟨⟨⟨hl0, hl1⟩, hv1, hv2⟩, ?_⟩
      show lam * v1.1 + (1 - lam) * v2.1 = μ0
      have : (lam * v1.1 + (1 - lam) * v2.1) * (v2.1 - v1.1) = μ0 * (v2.1 - v1.1) := by
        have : (lam * v1.1 + (1 - lam) * v2.1) * (v2.1 - v1.1) =
          (lam * (v2.1 - v1.1)) * v1.1 + ((1 - lam) * (v2.1 - v1.1)) * v2.1 := by ring
        rw [this, e1, e2]; ring
      exact mul_right_cancel₀ ht.ne' this
    have := hFle _ hmem
    simp only [hF] at this
    calc (v2.1 - μ0) * Gf M v1 + (μ0 - v1.1) * Gf M v2
        = (lam * Gf M v1 + (1 - lam) * Gf M v2) * (v2.1 - v1.1) := by
          rw [← e1, ← e2]; ring
      _ ≤ V * (v2.1 - v1.1) := mul_le_mul_of_nonneg_right this ht.le
  have hmid : ∀ v ∈ G, v.1 = μ0 → Gf M v ≤ V := by
    intro v hv he
    have hmem : ((1:ℝ), v, v) ∈ D := ⟨⟨⟨zero_le_one, le_refl _⟩, hv, hv⟩, by simp [he]⟩
    have := hFle _ hmem
    simp only [hF] at this
    linarith
  -- the slope of a supporting line
  obtain ⟨Sr, hSr⟩ : ∃ Sr : Set ℝ, Sr = {e | ∃ v ∈ G, μ0 < v.1 ∧ e = (Gf M v - V) / (v.1 - μ0)} :=
    ⟨_, rfl⟩
  have hSrne : Sr.Nonempty := ⟨_, by rw [hSr]; exact ⟨_, hw1, h1, rfl⟩⟩
  have hSrbdd : BddAbove Sr := by
    refine ⟨(V - Gf M ((0:ℝ), ps, (0:ℝ), (0:ℝ))) / μ0, ?_⟩
    rw [hSr]
    rintro e ⟨v, hv, hgt, rfl⟩
    have := hK _ hw0 v hv h0 hgt
    simp only at this
    rw [div_le_div_iff₀ (by linarith) h0]
    nlinarith
  obtain ⟨k, hk⟩ : ∃ k, k = sSup Sr := ⟨_, rfl⟩
  have hLall : ∀ v ∈ G, Gf M v ≤ V + k * (v.1 - μ0) := by
    intro v hv
    rcases lt_trichotomy v.1 μ0 with hlt | heq | hgt
    · have hk' : k ≤ (V - Gf M v) / (μ0 - v.1) := by
        rw [hk]
        apply csSup_le hSrne
        rw [hSr]
        rintro e ⟨u, hu, hgu, rfl⟩
        have := hK v hv u hu hlt hgu
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
      rw [le_div_iff₀ (by linarith)] at hk'
      nlinarith
    · rw [heq]; simp only [sub_self, mul_zero, add_zero]; exact hmid v hv heq
    · have : (Gf M v - V) / (v.1 - μ0) ≤ k := by
        rw [hk]; exact le_csSup hSrbdd (by rw [hSr]; exact ⟨v, hv, hgt, rfl⟩)
      rw [div_le_iff₀ (by linarith)] at this
      nlinarith
  -- W^C and the no-promotion surplus at p* lie below the supporting line
  have hWCL : ∀ x ∈ Set.Icc (0:ℝ) 1, WC M x ≤ V + k * (x - μ0) := by
    intro x hx
    apply WC_le M hM ps hps hps0 x hx
    intro p aH aL hg
    have := hLall _ ((mem_GrS M ps x p aH aL).2 hg)
    rwa [Gf_eq M x p aH aL hg.2.1] at this
  have hS0L : ∀ x ∈ Set.Icc (0:ℝ) 1, SSf M x ps 0 0 ≤ V + k * (x - μ0) := by
    intro x hx
    have a0 := hLall _ hw0
    have a1 := hLall _ hw1
    rw [Gf_eq M _ _ _ _ hps] at a0 a1
    simp only at a0 a1
    obtain ⟨hx0, hx1⟩ := hx
    have e : SSf M x ps 0 0 = (1 - x) * SSf M 0 ps 0 0 + x * SSf M 1 ps 0 0 := by
      simp only [SSf]; ring
    have e2 : V + k * (x - μ0) = (1 - x) * (V + k * (0 - μ0)) + x * (V + k * (1 - μ0)) := by
      ring
    rw [e, e2]
    nlinarith [mul_le_mul_of_nonneg_left a0 (by linarith : (0:ℝ) ≤ 1 - x),
      mul_le_mul_of_nonneg_left a1 hx0]
  -- the maximizer
  obtain ⟨⟨⟨hl0, hl1⟩, hv1, hv2⟩, hsum⟩ := hdst
  obtain ⟨l, ⟨x1, p1, b1, c1⟩, ⟨x2, p2, b2, c2⟩⟩ := dst
  simp only [Set.mem_ofPred_eq] at hsum
  simp only at hl0 hl1
  have hg1 := (mem_GrS M ps x1 p1 b1 c1).1 hv1
  have hg2 := (mem_GrS M ps x2 p2 b2 c2).1 hv2
  have hVe : V = l * SSf M x1 p1 b1 c1 + (1 - l) * SSf M x2 p2 b2 c2 := by
    rw [hV]; simp only [hF]; rw [Gf_eq M _ _ _ _ hg1.2.1, Gf_eq M _ _ _ _ hg2.2.1]
  have L1 := hLall _ hv1
  have L2 := hLall _ hv2
  rw [Gf_eq M _ _ _ _ hg1.2.1] at L1
  rw [Gf_eq M _ _ _ _ hg2.2.1] at L2
  simp only at L1 L2
  have hzero : l * (V + k * (x1 - μ0) - SSf M x1 p1 b1 c1) +
      (1 - l) * (V + k * (x2 - μ0) - SSf M x2 p2 b2 c2) = 0 := by
    linear_combination k * hsum + hVe
  have t1 : 0 ≤ l * (V + k * (x1 - μ0) - SSf M x1 p1 b1 c1) :=
    mul_nonneg hl0 (by linarith)
  have t2 : 0 ≤ (1 - l) * (V + k * (x2 - μ0) - SSf M x2 p2 b2 c2) :=
    mul_nonneg (by linarith) (by linarith)
  have z1 : l * (V + k * (x1 - μ0) - SSf M x1 p1 b1 c1) = 0 := by linarith
  have z2 : (1 - l) * (V + k * (x2 - μ0) - SSf M x2 p2 b2 c2) = 0 := by linarith
  have att1 : 0 < l → Att M x1 (p1, b1, c1) := by
    intro hl
    have hS : SSf M x1 p1 b1 c1 = V + k * (x1 - μ0) := by
      have := (mul_eq_zero.mp z1).resolve_left hl.ne'
      linarith
    refine attain M hM ps hmax hstrict x1 p1 b1 c1 hg1 ?_ ?_
    · rw [hS]; exact hS0L x1 hg1.1
    · rw [hS]; exact hWCL x1 hg1.1
  have att2 : 0 < 1 - l → Att M x2 (p2, b2, c2) := by
    intro hl
    have hS : SSf M x2 p2 b2 c2 = V + k * (x2 - μ0) := by
      have := (mul_eq_zero.mp z2).resolve_left hl.ne'
      linarith
    refine attain M hM ps hmax hstrict x2 p2 b2 c2 hg2 ?_ ?_
    · rw [hS]; exact hS0L x2 hg2.1
    · rw [hS]; exact hWCL x2 hg2.1
  have e1 : l * SSf M x1 p1 b1 c1 = l * WC M x1 := by
    rcases eq_or_lt_of_le hl0 with h | h
    · rw [← h]; ring
    · have := (att1 h).2
      rw [expSurplus_rule] at this
      rw [this]
  have e2 : (1 - l) * SSf M x2 p2 b2 c2 = (1 - l) * WC M x2 := by
    rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ 1 - l) with h | h
    · rw [← h]; ring
    · have := (att2 h).2
      rw [expSurplus_rule] at this
      rw [this]
  have hVe' : V = l * WC M x1 + (1 - l) * WC M x2 := by rw [hVe, e1, e2]
  refine ⟨l, x1, x2, (p1, b1, c1), (p2, b2, c2), hl0, hl1, hg1.1, hg2.1, hsum, att1, att2, ?_⟩
  apply co_eq_of
  · intro z hz
    rw [← hVe']
    exact hull_le (WC M) V k μ0 hWCL z hz
  · have hm := (convex_convexHull ℝ {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ WC M x.1})
      (subset_convexHull ℝ _ (⟨hg1.1, le_refl _⟩ : (x1, WC M x1) ∈
        {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ WC M x.1}))
      (subset_convexHull ℝ _ (⟨hg2.1, le_refl _⟩ : (x2, WC M x2) ∈
        {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ WC M x.1}))
      hl0 (by linarith : (0:ℝ) ≤ 1 - l) (by ring)
    have : l • (x1, WC M x1) + (1 - l) • (x2, WC M x2) =
        (μ0, l * WC M x1 + (1 - l) * WC M x2) := by
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; exact hsum
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [this] at hm
    exact hm

/-! ## Assembly -/

lemma bayes_mem (μ lH lL : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1) (hH : 0 ≤ lH) (hL : 0 ≤ lL) :
    bayes μ lH lL ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨h0, h1⟩ := hμ
  unfold bayes
  split_ifs with h
  · exact ⟨h0, h1⟩
  · have hA : 0 ≤ μ * lH := mul_nonneg h0 hH
    have hB : 0 ≤ (1 - μ) * lL := mul_nonneg (by linarith) hL
    have hpos : 0 < μ * lH + (1 - μ) * lL := lt_of_le_of_ne (by linarith) (Ne.symm h)
    refine ⟨div_nonneg hA hpos.le, ?_⟩
    rw [div_le_one hpos]; linarith

lemma term_eq2 (M : Market) (μ0 lH lL w x : ℝ) (hw : μ0 * lH + (1 - μ0) * lL = w)
    (hw0 : 0 ≤ w) (hpost : 0 < w → μ0 * lH / w = x) :
    (μ0 * lH + (1 - μ0) * lL) * WC M (bayes μ0 lH lL) = w * WC M x := by
  rw [hw]
  rcases eq_or_lt_of_le hw0 with h | h
  · rw [← h]; ring
  · have hb : bayes μ0 lH lL = x := by
      unfold bayes
      rw [hw, if_neg h.ne']
      exact hpost h
    rw [hb]

end CPSolOS

open CPSolOS

theorem solution (M : Market) (hM : M.Standing) (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0 : ℝ) 1) :
    ∃ sig : Signal 2, sig.IsValid ∧
      ∑ s, (μ0 * sig true s + (1 - μ0) * sig false s) *
          WC M (bayes μ0 (sig true s) (sig false s)) = co (WC M) μ0 := by
  obtain ⟨h0, h1⟩ := hμ0
  by_cases hend : μ0 * (1 - μ0) = 0
  · obtain ⟨sig, hsig⟩ : ∃ sig : Signal 2, sig = fun _ s => if s = 0 then 1 else 0 := ⟨_, rfl⟩
    have hv : sig.IsValid := by
      refine ⟨fun b s => ?_, fun b => ?_⟩
      · rw [hsig]; dsimp only; split_ifs <;> norm_num
      · rw [hsig, Fin.sum_univ_two]; simp
    refine ⟨sig, hv, ?_⟩
    rw [Fin.sum_univ_two]
    have s0t : sig true 0 = 1 := by rw [hsig]; simp
    have s0f : sig false 0 = 1 := by rw [hsig]; simp
    have s1t : sig true 1 = 0 := by rw [hsig]; simp
    have s1f : sig false 1 = 0 := by rw [hsig]; simp
    have t0 := term_eq2 M μ0 (sig true 0) (sig false 0) 1 μ0 (by rw [s0t, s0f]; ring) zero_le_one
      (by intro _; rw [s0t]; ring)
    have t1 := term_eq2 M μ0 (sig true 1) (sig false 1) 0 μ0 (by rw [s1t, s1f]; ring) (le_refl _)
      (by intro h; exact absurd h (lt_irrefl _))
    rw [t0, t1, co_endpoint M μ0 ⟨h0, h1⟩ hend]
    ring
  · have hμ0' : 0 < μ0 := by
      rcases eq_or_lt_of_le h0 with h | h
      · exact absurd (by rw [← h]; ring) hend
      · exact h
    have hμ1' : μ0 < 1 := by
      rcases eq_or_lt_of_le h1 with h | h
      · exact absurd (by rw [h]; ring) hend
      · exact h
    obtain ⟨l, x1, x2, w1, w2, hl0, hl1, hx1, hx2, hsum, _, _, hco⟩ :=
      interior_split M hM μ0 hμ0' hμ1'
    have hne0 : μ0 ≠ 0 := hμ0'.ne'
    have hne1 : 1 - μ0 ≠ 0 := by linarith
    obtain ⟨sig, hsig⟩ : ∃ sig : Signal 2, sig = fun b s =>
        if b then (if s = 0 then l * x1 / μ0 else (1 - l) * x2 / μ0)
        else (if s = 0 then l * (1 - x1) / (1 - μ0) else (1 - l) * (1 - x2) / (1 - μ0)) :=
      ⟨_, rfl⟩
    have s0t : sig true 0 = l * x1 / μ0 := by rw [hsig]; simp
    have s0f : sig false 0 = l * (1 - x1) / (1 - μ0) := by rw [hsig]; simp
    have s1t : sig true 1 = (1 - l) * x2 / μ0 := by rw [hsig]; simp
    have s1f : sig false 1 = (1 - l) * (1 - x2) / (1 - μ0) := by rw [hsig]; simp
    have hv : sig.IsValid := by
      obtain ⟨hx10, hx11⟩ := hx1
      obtain ⟨hx20, hx21⟩ := hx2
      have hl1' : 0 ≤ 1 - l := by linarith
      refine ⟨fun b s => ?_, fun b => ?_⟩
      · rcases b with _ | _ <;> fin_cases s
        · simp only [Fin.zero_eta]; rw [s0f]
          exact div_nonneg (mul_nonneg hl0 (by linarith)) (by linarith)
        · simp only [Fin.mk_one]; rw [s1f]
          exact div_nonneg (mul_nonneg hl1' (by linarith)) (by linarith)
        · simp only [Fin.zero_eta]; rw [s0t]
          exact div_nonneg (mul_nonneg hl0 hx10) (by linarith)
        · simp only [Fin.mk_one]; rw [s1t]
          exact div_nonneg (mul_nonneg hl1' hx20) (by linarith)
      · rw [Fin.sum_univ_two]
        rcases b with _ | _
        · rw [s0f, s1f]
          field_simp
          linarith
        · rw [s0t, s1t]
          field_simp
          linarith
    refine ⟨sig, hv, ?_⟩
    rw [Fin.sum_univ_two]
    have t0 := term_eq2 M μ0 (sig true 0) (sig false 0) l x1
      (by rw [s0t, s0f]; field_simp; ring) hl0
      (by intro h; rw [s0t]; field_simp)
    have t1 := term_eq2 M μ0 (sig true 1) (sig false 1) (1 - l) x2
      (by rw [s1t, s1f]; field_simp; ring) (by linarith)
      (by intro h; rw [s1t]; field_simp)
    rw [t0, t1, hco]
