-- Prove2me | solution 1 for ConfoundPromo.LongRun.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:17:44.794899+00:00
-- url     : https://prove2.me/submissions/88ca00f5-4cc0-463f-aa9f-4ca772244ac9

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

open ConfoundPromo.LongRun
open Finset

namespace CPSolP1

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

lemma saleProb_mem (M : Market) (hM : M.Standing) (b : Bool) (a p : ℝ)
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hp : p ∈ M.price) :
    saleProb M b a p ∈ Set.Icc (0:ℝ) 1 := by
  have hφ0 : 0 ≤ M.phiVal b := by
    unfold Market.phiVal; split_ifs <;> linarith [hM.phiL_pos, hM.phiL_lt_phiH]
  have hφ1 : M.phiVal b ≤ 1 := by
    unfold Market.phiVal; split_ifs <;> linarith [hM.phiL_lt_phiH, hM.phiH_lt_one]
  have hc := hM.rhoC_nonneg p hp
  have hc0 := hM.rhoC_le_rho0 p hp
  have h01 := hM.rho0_le_one p hp
  obtain ⟨ha0, ha1⟩ := ha
  unfold saleProb
  constructor
  · have : 0 ≤ M.phiVal b * a * M.rho0 p := by
      apply mul_nonneg (mul_nonneg hφ0 ha0); linarith
    have : 0 ≤ (1 - M.phiVal b) * M.rhoC p := mul_nonneg (by linarith) hc
    linarith
  · have : M.phiVal b * a * M.rho0 p ≤ M.phiVal b * M.rho0 p := by
      have : 0 ≤ M.rho0 p := by linarith
      nlinarith [mul_nonneg hφ0 this]
    have : (1 - M.phiVal b) * M.rhoC p ≤ (1 - M.phiVal b) * M.rho0 p :=
      mul_le_mul_of_nonneg_left hc0 (by linarith)
    nlinarith

lemma likelihood_nonneg (M : Market) (hM : M.Standing) (b : Bool) (a p : ℝ)
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hp : p ∈ M.price) (y : Bool) :
    0 ≤ likelihood M b a p y := by
  have h := saleProb_mem M hM b a p ha hp
  unfold likelihood; split_ifs
  · exact h.1
  · linarith [h.2]

lemma belief_mem (M : Market) (hM : M.Standing) {n T : ℕ} (μ0 : ℝ)
    (hμ0 : μ0 ∈ Set.Icc (0:ℝ) 1) (sig : Signal n) (hsig : sig.IsValid) (α : Promo n T)
    (hα : α.IsValid) : ∀ (t : ℕ) (h : SHist n t), h.InPrice M →
      belief M μ0 sig α t h ∈ Set.Icc (0:ℝ) 1 := by
  intro t
  induction t with
  | zero =>
    intro h _
    simp only [belief]
    exact bayes_mem _ _ _ hμ0 (hsig.1 _ _) (hsig.1 _ _)
  | succ t ih =>
    intro h hh
    simp only [belief]
    have hinit : h.init.InPrice M := by
      intro i
      have := hh i.castSucc
      simpa [SHist.init, Fin.init] using this
    have hlast : h.last.1 ∈ M.price := hh (Fin.last t)
    have hαm : ∀ b, α.at t h.last.1 b h.init ∈ Set.Icc (0:ℝ) 1 := by
      intro b
      unfold Promo.at
      split_ifs
      · exact hα _ _ _ _
      · exact ⟨le_refl _, zero_le_one⟩
    exact bayes_mem _ _ _ (ih _ hinit) (likelihood_nonneg M hM _ _ _ (hαm true) hlast _)
      (likelihood_nonneg M hM _ _ _ (hαm false) hlast _)

lemma histAt_succ_init {n T : ℕ} (π : Pricing n T) (s : Fin n) (y : Fin T → Bool) (t : ℕ) :
    (histAt π s y (t+1)).init = histAt π s y t := by
  simp only [histAt, SHist.snoc, SHist.init, Fin.init_snoc]

lemma histAt_succ_last {n T : ℕ} (π : Pricing n T) (s : Fin n) (y : Fin T → Bool) (t : ℕ) :
    (histAt π s y (t+1)).last = (π.at t (histAt π s y t), yAt y t) := by
  simp only [histAt, SHist.snoc, SHist.last, Fin.snoc_last]

lemma bayes_mul (μ lT lF : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1) (hT : 0 ≤ lT) (hF : 0 ≤ lF) :
    (μ * lT + (1 - μ) * lF) * bayes μ lT lF = μ * lT := by
  obtain ⟨h0, h1⟩ := hμ
  unfold bayes
  split_ifs with h
  · have : μ * lT = 0 := by
      have := mul_nonneg h0 hT; have := mul_nonneg (by linarith : 0 ≤ 1 - μ) hF; linarith
    rw [h, this]; ring
  · field_simp

/-- Beliefs under the belief-based policy that applies `rule μ` at belief `μ`. -/
noncomputable def beliefR (M : Market) {n : ℕ} (T : ℕ) (μ0 : ℝ) (sig : Signal n)
    (rule : ℝ → ℝ → Bool → ℝ) : (t : ℕ) → SHist n t → ℝ
  | 0, h => bayes μ0 (sig true h.1) (sig false h.1)
  | t + 1, h =>
      bayes (beliefR M T μ0 sig rule t h.init)
        (likelihood M true (if t < T then rule (beliefR M T μ0 sig rule t h.init) h.last.1 true
          else 0) h.last.1 h.last.2)
        (likelihood M false (if t < T then rule (beliefR M T μ0 sig rule t h.init) h.last.1 false
          else 0) h.last.1 h.last.2)

lemma belief_eq_beliefR (M : Market) {n : ℕ} (T : ℕ) (μ0 : ℝ) (sig : Signal n)
    (rule : ℝ → ℝ → Bool → ℝ) :
    ∀ (t : ℕ) (h : SHist n t),
      belief M μ0 sig (fun (t : Fin T) q b h => rule (beliefR M T μ0 sig rule t h) q b) t h =
        beliefR M T μ0 sig rule t h := by
  intro t
  induction t with
  | zero => intro h; simp [belief, beliefR]
  | succ t ih =>
    intro h
    rw [belief, beliefR, ih]
    simp only [Promo.at, dite_eq_ite]

lemma histAt_dep {n T : ℕ} (π : Pricing n T) (s : Fin n) (y y' : Fin T → Bool) :
    ∀ t : ℕ, (∀ i : Fin T, (i : ℕ) < t → y i = y' i) → histAt π s y t = histAt π s y' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    have h1 := ih (fun i hi => h i (by omega))
    have h2 : yAt y t = yAt y' t := by
      unfold yAt
      split_ifs with ht
      · exact h ⟨t, ht⟩ (by simp)
      · rfl
    simp only [histAt, h1, h2]

lemma histAt_inPrice (M : Market) {n T : ℕ} (μ0 : ℝ) (sig : Signal n) (α : Promo n T)
    (π : Pricing n T) (hπ : IsMyopic M μ0 sig α π) (s : Fin n) (y : Fin T → Bool) :
    ∀ t : ℕ, t ≤ T → (histAt π s y t).InPrice M := by
  intro t
  induction t with
  | zero => intro _ i; exact i.elim0
  | succ t ih =>
    intro ht
    have hih := ih (by omega)
    have htT : t < T := by omega
    have hp : π.at t (histAt π s y t) ∈ M.price := by
      simp only [Pricing.at, htT, dif_pos]
      exact (hπ ⟨t, htT⟩ _ hih).1
    intro i
    simp only [histAt, SHist.snoc]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; exact hp
    · simp only [Fin.snoc_castSucc]; exact hih j

section Path

variable (M : Market) {n T : ℕ} (α : Promo n T) (π : Pricing n T) (b : Bool) (s : Fin n)

/-- The likelihood factor of period `t`. -/
def LL (t : Fin T) (y : Fin T → Bool) : ℝ :=
  likelihood M b (promoAt α π b s y t) (priceAt π s y t) (y t)

/-- Partial product over periods `< k`. -/
def PP (k : ℕ) (y : Fin T → Bool) : ℝ :=
  ∏ t : Fin T, if (t : ℕ) < k then LL M α π b s t y else 1

def Dep (k : ℕ) (G : (Fin T → Bool) → ℝ) : Prop :=
  ∀ y y' : Fin T → Bool, (∀ i : Fin T, (i : ℕ) < k → y i = y' i) → G y = G y'

lemma PP_zero (y : Fin T → Bool) : PP M α π b s 0 y = 1 := by
  simp [PP]

lemma PP_T (y : Fin T → Bool) : PP M α π b s T y = pathProb M α π b s y := by
  unfold PP pathProb LL
  apply Finset.prod_congr rfl
  intro t _
  simp [t.isLt]

lemma PP_succ (k : Fin T) (y : Fin T → Bool) :
    PP M α π b s (k + 1) y = PP M α π b s k y * LL M α π b s k y := by
  unfold PP
  have : ∀ t : Fin T, (if (t : ℕ) < (k : ℕ) + 1 then LL M α π b s t y else 1) =
      (if (t : ℕ) < k then LL M α π b s t y else 1) * (if t = k then LL M α π b s t y else 1) := by
    intro t
    by_cases h1 : (t : ℕ) < k
    · have : t ≠ k := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      simp [h1, this, show (t : ℕ) < k + 1 by omega]
    · by_cases h2 : t = k
      · subst h2; simp
      · have : ¬ ((t : ℕ) < k + 1) := by
          intro h; apply h2; apply Fin.ext; omega
        simp [h1, h2, this]
  rw [Finset.prod_congr rfl (fun t _ => this t), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite_eq']
  simp

lemma LL_dep (t : Fin T) : Dep (T := T) ((t : ℕ) + 1) (LL M α π b s t) := by
  intro y y' h
  have hh : histAt π s y t = histAt π s y' t := histAt_dep π s y y' t (fun i hi => h i (by omega))
  unfold LL promoAt priceAt
  rw [hh, h t (by omega)]

lemma PP_dep (k : ℕ) : Dep (T := T) k (PP M α π b s k) := by
  intro y y' h
  unfold PP
  apply Finset.prod_congr rfl
  intro t _
  split_ifs with ht
  · exact LL_dep M α π b s t y y' (fun i hi => h i (by omega))
  · rfl

def flipAt (k : Fin T) (y : Fin T → Bool) : Fin T → Bool := Function.update y k (!(y k))

lemma flipAt_invol (k : Fin T) : Function.Involutive (flipAt (T := T) k) := by
  intro y
  unfold flipAt
  funext i
  by_cases h : i = k
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma flipAt_agree (k : Fin T) (y : Fin T → Bool) :
    ∀ i : Fin T, (i : ℕ) < k → flipAt k y i = y i := by
  intro i hi
  have : i ≠ k := fun h => by rw [h] at hi; exact lt_irrefl _ hi
  simp [flipAt, Function.update_of_ne this]

lemma sum_flip (k : Fin T) (F : (Fin T → Bool) → ℝ) :
    ∑ y, F (flipAt k y) = ∑ y, F y :=
  Fintype.sum_equiv ((flipAt_invol k).toPerm _) _ _ (fun _ => rfl)

lemma LL_flip_add (k : Fin T) (y : Fin T → Bool) :
    LL M α π b s k y + LL M α π b s k (flipAt k y) = 1 := by
  have hh : histAt π s (flipAt k y) k = histAt π s y k :=
    histAt_dep π s _ _ k (flipAt_agree k y)
  unfold LL promoAt priceAt
  rw [hh]
  have : flipAt k y k = !(y k) := by simp [flipAt]
  rw [this]
  cases y k <;> simp [likelihood]

lemma marg_step (k : Fin T) (G : (Fin T → Bool) → ℝ) (hG : Dep (T := T) k G) :
    ∑ y, PP M α π b s (k + 1) y * G y = (1/2) * ∑ y, PP M α π b s k y * G y := by
  have e1 : ∑ y, PP M α π b s (k + 1) y * G y =
      ∑ y, PP M α π b s k y * LL M α π b s k y * G y := by
    apply Finset.sum_congr rfl; intro y _; rw [PP_succ]
  have e2 : ∑ y, PP M α π b s k y * LL M α π b s k y * G y =
      ∑ y, PP M α π b s k y * LL M α π b s k (flipAt k y) * G y := by
    rw [← sum_flip k (fun y => PP M α π b s k y * LL M α π b s k y * G y)]
    apply Finset.sum_congr rfl; intro y _
    rw [PP_dep M α π b s k (flipAt k y) y (flipAt_agree k y), hG (flipAt k y) y (flipAt_agree k y)]
  have e3 : ∑ y, PP M α π b s k y * LL M α π b s k y * G y +
      ∑ y, PP M α π b s k y * LL M α π b s k (flipAt k y) * G y =
      ∑ y, PP M α π b s k y * G y := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro y _
    have := LL_flip_add M α π b s k y
    linear_combination (PP M α π b s k y * G y) * this
  rw [e1]
  linarith

lemma marg_iter (j : ℕ) (G : (Fin T → Bool) → ℝ) (hG : Dep (T := T) j G) :
    ∀ m : ℕ, j ≤ m → m ≤ T →
      ∑ y, PP M α π b s m y * G y = (1/2) ^ (m - j) * ∑ y, PP M α π b s j y * G y := by
  intro m
  induction m with
  | zero =>
    intro hj _
    have : j = 0 := by omega
    subst this; simp
  | succ m ih =>
    intro hj hm
    rcases Nat.eq_or_lt_of_le hj with h | h
    · subst h; simp
    · have hmT : m < T := by omega
      have hGm : Dep (T := T) m G := fun y y' hyy => hG y y' (fun i hi => hyy i (by omega))
      have := marg_step M α π b s ⟨m, hmT⟩ G hGm
      simp only at this
      rw [this, ih (by omega) (by omega)]
      rw [show m + 1 - j = (m - j) + 1 by omega, pow_succ]
      ring

lemma sum_PP_T : ∑ y, pathProb M α π b s y = 1 := by
  have h := marg_iter M α π b s 0 (fun _ => 1) (fun _ _ _ => rfl) T (Nat.zero_le _) le_rfl
  simp only [mul_one, PP_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.sub_zero] at h
  rw [← Finset.sum_congr rfl (fun y _ => PP_T M α π b s y), h]
  rw [← mul_pow]; norm_num

end Path

/-- Belief relation: posterior times normalizer equals the joint weight of `φ_H`. -/
lemma bayes_rel (μ N D lT lF : ℝ) (hN : 0 ≤ N) (hDN : 0 ≤ D - N) (hT : 0 ≤ lT) (hF : 0 ≤ lF)
    (hμ : μ * D = N) :
    bayes μ lT lF * (N * lT + (D - N) * lF) = N * lT := by
  rcases eq_or_lt_of_le (show 0 ≤ D by linarith) with hD | hD
  · have hN0 : N = 0 := by linarith
    rw [← hD, hN0]; ring
  · have hμe : μ = N / D := by field_simp; linarith
    unfold bayes
    have hden : μ * lT + (1 - μ) * lF = (N * lT + (D - N) * lF) / D := by
      rw [hμe]; field_simp
    split_ifs with h
    · rw [hden] at h
      have h0 : N * lT + (D - N) * lF = 0 := by
        rcases div_eq_zero_iff.mp h with h | h
        · exact h
        · exact absurd h hD.ne'
      have : N * lT = 0 := by
        have := mul_nonneg hN hT; have := mul_nonneg hDN hF; linarith
      rw [h0, this]; ring
    · rw [hden]
      have hne : N * lT + (D - N) * lF ≠ 0 := by
        intro h0; apply h; rw [hden, h0, zero_div]
      rw [hμe]
      field_simp

/-! ## Single-price promotion is without loss for a myopic choice (Proposition 1, step 1) -/

lemma rhoC_pos_neg (M : Market) (hM : M.Standing) (q : ℝ) (hq : q ∈ M.price) (hq0 : q < 0) :
    0 < M.rhoC q := by
  by_contra hcon
  have hz : M.rhoC q = 0 := le_antisymm (not_lt.mp hcon) (hM.rhoC_nonneg q hq)
  have h0P : (0:ℝ) ∈ M.price := ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩
  have hs := hM.revC_strictConcave.2 hq h0P (ne_of_lt hq0) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  have hm : (1/2 : ℝ) • q + (1/2 : ℝ) • (0:ℝ) ∈ M.price :=
    (convex_Icc M.pLo M.pHi) hq h0P (by norm_num) (by norm_num) (by norm_num)
  have hnn := hM.rhoC_nonneg _ hm
  simp only [smul_eq_mul, hz, mul_zero, zero_mul, add_zero] at hs hnn
  nlinarith

lemma expRev_split (M : Market) (μ : ℝ) (a : ℝ → Bool → ℝ) (q : ℝ) :
    expRev M μ a q = cc M μ * (q * M.rhoC q) +
      q * M.rho0 q * (μ * M.phiH * a q true + (1 - μ) * M.phiL * a q false) := by
  simp only [expRev, cc, saleProb, Market.phiVal, if_true, Bool.false_eq_true, if_false]
  ring

lemma expSurplus_split (M : Market) (μ : ℝ) (a : ℝ → Bool → ℝ) (q : ℝ) :
    expSurplus M μ a q = SSf M μ q 0 0 +
      (μ * M.phiH * a q true + (1 - μ) * M.phiL * a q false) * (M.W0 q - M.Wout) := by
  simp only [expSurplus, SSf, surplus, Market.phiVal, if_true, Bool.false_eq_true, if_false]
  ring

lemma single_price_myopic (M : Market) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1)
    (a : ℝ → Bool → ℝ) (ha : IsValidRule a) (p : ℝ) (hmy : IsMyopicChoice M μ a p) :
    IsMyopicChoice M μ (rule (p, a p true, a p false)) p := by
  obtain ⟨ps, hps, hps0, hmax, hstrict⟩ := exists_pstar M hM
  obtain ⟨hp, hrev, htie⟩ := hmy
  have hφL := hM.phiL_pos
  have hφLH := hM.phiL_lt_phiH
  have hφH := hM.phiH_lt_one
  obtain ⟨hμ0, hμ1⟩ := hμ
  have hcc := cc_pos M hM μ ⟨hμ0, hμ1⟩
  have e_p : expRev M μ (rule (p, a p true, a p false)) p = expRev M μ a p := by
    rw [expRev_rule]; rfl
  have es_p : expSurplus M μ (rule (p, a p true, a p false)) p = expSurplus M μ a p := by
    rw [expSurplus_rule]; rfl
  have h0P : (0:ℝ) ∈ M.price := ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩
  have hrev0 : 0 ≤ expRev M μ a p := by
    have := hrev 0 h0P
    simp only [expRev, zero_mul] at this
    exact this
  -- promotion revenue is nonnegative at nonnegative prices
  have hprom : ∀ q ∈ M.price, 0 ≤ q →
      0 ≤ q * M.rho0 q * (μ * M.phiH * a q true + (1 - μ) * M.phiL * a q false) := by
    intro q hq hq0
    have h1 := (ha q true).1
    have h2 := (ha q false).1
    have hr0 := le_trans (hM.rhoC_nonneg q hq) (hM.rhoC_le_rho0 q hq)
    apply mul_nonneg (mul_nonneg hq0 hr0)
    exact add_nonneg (mul_nonneg (mul_nonneg hμ0 (by linarith)) h1)
      (mul_nonneg (mul_nonneg (by linarith) hφL.le) h2)
  have hle : ∀ q ∈ M.price, q ≠ p → cc M μ * (q * M.rhoC q) ≤ expRev M μ a p := by
    intro q hq hqp
    rcases le_or_gt 0 q with hq0 | hq0
    · have := hrev q hq
      rw [expRev_split] at this
      linarith [hprom q hq hq0]
    · have : q * M.rhoC q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hq0.le (hM.rhoC_nonneg q hq)
      nlinarith
  refine ⟨hp, ?_, ?_⟩
  · intro q hq
    by_cases hqp : q = p
    · rw [hqp]
    · rw [expRev_rule_ne M μ p _ _ q hqp, e_p]
      exact hle q hq hqp
  · intro q hq heq
    by_cases hqp : q = p
    · rw [hqp]
    · rw [expRev_rule_ne M μ p _ _ q hqp, e_p] at heq
      rw [expSurplus_rule_ne M μ p _ _ q hqp, es_p]
      -- the revenue at `p` is positive
      have hpos : 0 < expRev M μ a p := by
        by_contra hnp
        have hz : expRev M μ a p = 0 := le_antisymm (not_lt.mp hnp) hrev0
        have hm0 : ps * M.rhoC ps = 0 := by
          have h1 := hrev ps hps
          rw [expRev_split] at h1
          have h2 := hprom ps hps hps0
          have h3 : 0 ≤ ps * M.rhoC ps := mul_nonneg hps0 (hM.rhoC_nonneg ps hps)
          have h4 : cc M μ * (ps * M.rhoC ps) ≤ 0 := by linarith
          have h5 : ps * M.rhoC ps ≤ 0 := by
            by_contra h6; push_neg at h6; nlinarith
          linarith
        have hps_eq : ps = 0 := by
          by_contra hne
          have := hstrict 0 h0P (Ne.symm hne)
          simp at this; linarith
        rcases lt_trichotomy p 0 with hpn | hpz | hpp
        · have hcp := rhoC_pos_neg M hM p hp hpn
          have hsale : 0 < μ * saleProb M true (a p true) p + (1 - μ) * saleProb M false (a p false) p := by
            have e := expRev_split M μ a p
            have hsH := saleProb_nonneg M hM true (a p true) p (ha p true) hp
            have hsL := saleProb_nonneg M hM false (a p false) p (ha p false) hp
            have hr0 := le_trans (hM.rhoC_nonneg p hp) (hM.rhoC_le_rho0 p hp)
            unfold saleProb Market.phiVal
            simp only [if_true, Bool.false_eq_true, if_false]
            have h1 := (ha p true).1
            have h2 := (ha p false).1
            have : 0 < μ * (1 - M.phiH) * M.rhoC p + (1 - μ) * (1 - M.phiL) * M.rhoC p := by
              have : μ * (1 - M.phiH) * M.rhoC p + (1 - μ) * (1 - M.phiL) * M.rhoC p =
                cc M μ * M.rhoC p := by unfold cc; ring
              rw [this]; exact mul_pos hcc hcp
            nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hμ0 (by linarith : (0:ℝ) ≤ M.phiH)) h1) hr0,
              mul_nonneg (mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - μ) hφL.le) h2) hr0]
          have : expRev M μ a p < 0 := by
            unfold expRev; exact mul_neg_of_neg_of_pos hpn hsale
          linarith
        · -- p = 0, so q ≠ 0
          have hq0 : q ≠ 0 := by rw [← hpz]; exact hqp
          have hqs := hstrict q hq (by rw [hps_eq]; exact hq0)
          rw [hm0] at hqs
          rw [hz] at heq
          have : cc M μ * (q * M.rhoC q) < 0 := mul_neg_of_pos_of_neg hcc hqs
          linarith
        · have hps' := hstrict p hp (by rw [hps_eq]; exact hpp.ne')
          rw [hm0] at hps'
          have : 0 ≤ p * M.rhoC p := mul_nonneg hpp.le (hM.rhoC_nonneg p hp)
          linarith
      -- hence `q > 0` and the promotion at `q` carries no weight
      have hqpos : 0 < q * M.rhoC q := by
        by_contra h; push_neg at h
        have : cc M μ * (q * M.rhoC q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcc.le h
        linarith
      have hq0 : 0 < q := by
        by_contra h; push_neg at h
        have : q * M.rhoC q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (hM.rhoC_nonneg q hq)
        linarith
      have hrc : 0 < M.rhoC q := by
        by_contra h; push_neg at h
        have : q * M.rhoC q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0.le h
        linarith
      have hr0 : 0 < M.rho0 q := lt_of_lt_of_le hrc (hM.rhoC_le_rho0 q hq)
      have hrq := hrev q hq
      rw [expRev_split] at hrq
      have hw : μ * M.phiH * a q true + (1 - μ) * M.phiL * a q false = 0 := by
        have hpr := hprom q hq hq0.le
        have hzero : q * M.rho0 q * (μ * M.phiH * a q true + (1 - μ) * M.phiL * a q false) = 0 := by
          linarith
        have hqr : q * M.rho0 q ≠ 0 := (mul_pos hq0 hr0).ne'
        exact (mul_eq_zero.mp hzero).resolve_left hqr
      have hrevq : expRev M μ a q = expRev M μ a p := by
        rw [expRev_split, hw]; linarith
      have := htie q hq hrevq
      rw [expSurplus_split M μ a q, hw] at this
      linarith

/-! ## Recursive continuation values -/

/-- Predictive probability of the sale outcome `y` at belief `μ`. -/
def pr (M : Market) (μ aH aL p : ℝ) (y : Bool) : ℝ :=
  μ * likelihood M true aH p y + (1 - μ) * likelihood M false aL p y

lemma pr_nonneg (M : Market) (hM : M.Standing) (μ aH aL p : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1)
    (haH : aH ∈ Set.Icc (0:ℝ) 1) (haL : aL ∈ Set.Icc (0:ℝ) 1) (hp : p ∈ M.price) (y : Bool) :
    0 ≤ pr M μ aH aL p y := by
  unfold pr
  exact add_nonneg (mul_nonneg hμ.1 (likelihood_nonneg M hM _ _ _ haH hp y))
    (mul_nonneg (by linarith [hμ.2]) (likelihood_nonneg M hM _ _ _ haL hp y))

/-- Continuation value with `k` periods remaining, from period `t` at history `h`. -/
noncomputable def Wk (M : Market) {n T : ℕ} (μ0 : ℝ) (sig : Signal n) (α : Promo n T)
    (π : Pricing n T) : ℕ → (t : ℕ) → SHist n t → ℝ
  | 0, _, _ => 0
  | k + 1, t, h =>
      expSurplus M (belief M μ0 sig α t h) (fun q b => α.at t q b h) (π.at t h) +
      ∑ y : Bool, pr M (belief M μ0 sig α t h) (α.at t (π.at t h) true h)
          (α.at t (π.at t h) false h) (π.at t h) y *
        Wk M μ0 sig α π k (t + 1) (h.snoc (π.at t h, y))

lemma flip2 {T : ℕ} (k : Fin T) (G : (Fin T → Bool) → Bool → ℝ)
    (hG : ∀ c (y y' : Fin T → Bool), (∀ i : Fin T, (i : ℕ) < k → y i = y' i) → G y c = G y' c) :
    ∑ y, ∑ c, G y c = 2 * ∑ y, G y (y k) := by
  have h1 : ∑ y, G y (y k) = ∑ y, G y (!(y k)) := by
    rw [← sum_flip k (fun y => G y (y k))]
    apply Finset.sum_congr rfl
    intro y _
    have e : flipAt k y k = !(y k) := by simp [flipAt]
    rw [e, hG _ (flipAt k y) y (flipAt_agree k y)]
  have h2 : ∀ y : Fin T → Bool, ∑ c, G y c = G y (y k) + G y (!(y k)) := by
    intro y
    rw [Fintype.sum_bool]
    cases y k <;> simp [add_comm]
  rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_add_distrib, ← h1]
  ring

section Value

variable (M : Market) {n T : ℕ} (μ0 : ℝ) (sig : Signal n) (α : Promo n T) (π : Pricing n T)

/-- joint weight of state `b`, signal `s` and the first `t` outcomes of `y` -/
def JJ (b : Bool) (t : ℕ) (s : Fin n) (y : Fin T → Bool) : ℝ :=
  prior μ0 b * sig b s * PP M α π b s t y

/-- total weight of the history -/
def JH (t : ℕ) (s : Fin n) (y : Fin T → Bool) : ℝ :=
  JJ M μ0 sig α π true t s y + JJ M μ0 sig α π false t s y

/-- likelihood of the period-`t` outcome on the path -/
def lik (b : Bool) (t : ℕ) (s : Fin n) (y : Fin T → Bool) : ℝ :=
  likelihood M b (α.at t (π.at t (histAt π s y t)) b (histAt π s y t))
    (π.at t (histAt π s y t)) (yAt y t)

lemma LL_eq (b : Bool) (s : Fin n) (t : Fin T) (y : Fin T → Bool) :
    LL M α π b s t y = lik M α π b t s y := by
  simp [LL, lik, promoAt, priceAt, yAt, t.isLt]

lemma JJ_succ (b : Bool) (t : ℕ) (ht : t < T) (s : Fin n) (y : Fin T → Bool) :
    JJ M μ0 sig α π b (t + 1) s y = JJ M μ0 sig α π b t s y * lik M α π b t s y := by
  unfold JJ
  have := PP_succ M α π b s ⟨t, ht⟩ y
  simp only at this
  rw [this, LL_eq]
  ring

lemma belief_succ_path (t : ℕ) (s : Fin n) (y : Fin T → Bool) :
    belief M μ0 sig α (t + 1) (histAt π s y (t + 1)) =
      bayes (belief M μ0 sig α t (histAt π s y t)) (lik M α π true t s y)
        (lik M α π false t s y) := by
  rw [belief, histAt_succ_init, histAt_succ_last]
  rfl

end Value

section ValueRep

variable (M : Market) (hM : M.Standing) {n T : ℕ} (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0:ℝ) 1)
  (sig : Signal n) (hsig : sig.IsValid) (α : Promo n T) (hα : α.IsValid) (π : Pricing n T)
  (hπ : IsMyopic M μ0 sig α π)

include hα in
lemma promo_mem (t : ℕ) (q : ℝ) (b : Bool) (h : SHist n t) : α.at t q b h ∈ Set.Icc (0:ℝ) 1 := by
  unfold Promo.at
  split_ifs
  · exact hα _ _ _ _
  · exact ⟨le_refl _, zero_le_one⟩

include hπ in
lemma price_mem (s : Fin n) (y : Fin T → Bool) (t : ℕ) (ht : t < T) :
    π.at t (histAt π s y t) ∈ M.price := by
  have hin := histAt_inPrice M μ0 sig α π hπ s y t ht.le
  simp only [Pricing.at, ht, dif_pos]
  exact (hπ ⟨t, ht⟩ _ hin).1

include hM hα hπ in
lemma lik_nonneg (b : Bool) (t : ℕ) (ht : t < T) (s : Fin n) (y : Fin T → Bool) :
    0 ≤ lik M α π b t s y :=
  likelihood_nonneg M hM _ _ _ (promo_mem α hα _ _ _ _) (price_mem M μ0 sig α π hπ s y t ht) _

include hM hα hπ in
lemma PP_nonneg (b : Bool) (s : Fin n) (t : ℕ) (y : Fin T → Bool) : 0 ≤ PP M α π b s t y := by
  unfold PP
  apply Finset.prod_nonneg
  intro t' _
  split_ifs
  · rw [LL_eq]; exact lik_nonneg M hM μ0 sig α hα π hπ b t' t'.isLt s y
  · exact zero_le_one

include hM hμ0 hsig hα hπ in
lemma JJ_nonneg (b : Bool) (t : ℕ) (s : Fin n) (y : Fin T → Bool) :
    0 ≤ JJ M μ0 sig α π b t s y := by
  unfold JJ prior
  apply mul_nonneg (mul_nonneg _ (hsig.1 b s)) (PP_nonneg M hM μ0 sig α hα π hπ b s t y)
  split_ifs
  · exact hμ0.1
  · linarith [hμ0.2]

include hM hμ0 hsig hα hπ in
lemma BR (s : Fin n) (y : Fin T → Bool) : ∀ t, t ≤ T →
    belief M μ0 sig α t (histAt π s y t) * JH M μ0 sig α π t s y = JJ M μ0 sig α π true t s y := by
  intro t
  induction t with
  | zero =>
    intro _
    have hb := bayes_mul μ0 (sig true s) (sig false s) hμ0 (hsig.1 _ _) (hsig.1 _ _)
    simp only [JH, JJ, PP_zero, prior, if_true, Bool.false_eq_true, if_false, belief, histAt]
    linear_combination hb
  | succ t ih =>
    intro ht
    have htT : t < T := by omega
    have IH := ih (by omega)
    rw [belief_succ_path]
    unfold JH
    rw [JJ_succ M μ0 sig α π true t htT, JJ_succ M μ0 sig α π false t htT]
    have hN := JJ_nonneg M hM μ0 hμ0 sig hsig α hα π hπ true t s y
    have hL := JJ_nonneg M hM μ0 hμ0 sig hsig α hα π hπ false t s y
    have hrel := bayes_rel (belief M μ0 sig α t (histAt π s y t)) (JJ M μ0 sig α π true t s y)
      (JH M μ0 sig α π t s y) (lik M α π true t s y) (lik M α π false t s y) hN
      (by unfold JH; linarith) (lik_nonneg M hM μ0 sig α hα π hπ true t htT s y)
      (lik_nonneg M hM μ0 sig α hα π hπ false t htT s y) IH
    have e : JH M μ0 sig α π t s y - JJ M μ0 sig α π true t s y = JJ M μ0 sig α π false t s y := by
      unfold JH; ring
    rw [e] at hrel
    exact hrel

/-- the predictive probability of the period-`t` outcome on the path -/
noncomputable def prPath (t : ℕ) (s : Fin n) (y : Fin T → Bool) (c : Bool) : ℝ :=
  pr M (belief M μ0 sig α t (histAt π s y t)) (α.at t (π.at t (histAt π s y t)) true (histAt π s y t))
    (α.at t (π.at t (histAt π s y t)) false (histAt π s y t)) (π.at t (histAt π s y t)) c

include hM hμ0 hsig hα hπ in
lemma JH_succ (t : ℕ) (ht : t < T) (s : Fin n) (y : Fin T → Bool) :
    JH M μ0 sig α π (t + 1) s y = JH M μ0 sig α π t s y * prPath M μ0 sig α π t s y (yAt y t) := by
  have hbr := BR M hM μ0 hμ0 sig hsig α hα π hπ s y t ht.le
  unfold JH
  rw [JJ_succ M μ0 sig α π true t ht, JJ_succ M μ0 sig α π false t ht]
  unfold prPath pr lik at *
  unfold JH at hbr
  linear_combination (likelihood M false (α.at t (π.at t (histAt π s y t)) false (histAt π s y t))
      (π.at t (histAt π s y t)) (yAt y t) -
    likelihood M true (α.at t (π.at t (histAt π s y t)) true (histAt π s y t))
      (π.at t (histAt π s y t)) (yAt y t)) * hbr

/-- expected surplus of period `t` -/
def EE (t : Fin T) : ℝ :=
  ∑ b, prior μ0 b * ∑ s, sig b s * ∑ y, pathProb M α π b s y *
    surplus M b (promoAt α π b s y t) (priceAt π s y t)

/-- current expected surplus at the period-`t` history of the path -/
noncomputable def eS (t : ℕ) (s : Fin n) (y : Fin T → Bool) : ℝ :=
  expSurplus M (belief M μ0 sig α t (histAt π s y t)) (fun q b => α.at t q b (histAt π s y t))
    (π.at t (histAt π s y t))

include hM hμ0 hsig hα hπ in
lemma EE_eq (t : Fin T) :
    EE M μ0 sig α π t = (1/2) ^ (T - t) * ∑ s, ∑ y, JH M μ0 sig α π t s y * eS M μ0 sig α π t s y := by
  have hm : ∀ b s, ∑ y, pathProb M α π b s y * surplus M b (promoAt α π b s y t) (priceAt π s y t) =
      (1/2) ^ (T - t) * ∑ y, PP M α π b s t y * surplus M b (promoAt α π b s y t) (priceAt π s y t) := by
    intro b s
    have hdep : Dep (T := T) t (fun y => surplus M b (promoAt α π b s y t) (priceAt π s y t)) := by
      intro y y' hyy
      have hh : histAt π s y t = histAt π s y' t := histAt_dep π s y y' t hyy
      simp only [promoAt, priceAt, hh]
    have := marg_iter M α π b s t _ hdep T t.isLt.le le_rfl
    rw [← this]
    apply Finset.sum_congr rfl
    intro y _
    rw [PP_T]
  have key : ∀ s y, JH M μ0 sig α π t s y * eS M μ0 sig α π t s y =
      JJ M μ0 sig α π true t s y * surplus M true (promoAt α π true s y t) (priceAt π s y t) +
      JJ M μ0 sig α π false t s y * surplus M false (promoAt α π false s y t) (priceAt π s y t) := by
    intro s y
    have hbr := BR M hM μ0 hμ0 sig hsig α hα π hπ s y t t.isLt.le
    unfold JH at *
    unfold eS expSurplus
    simp only [promoAt, priceAt]
    linear_combination
      (surplus M true (α.at (↑t) (π.at (↑t) (histAt π s y ↑t)) true (histAt π s y ↑t))
        (π.at (↑t) (histAt π s y ↑t)) -
       surplus M false (α.at (↑t) (π.at (↑t) (histAt π s y ↑t)) false (histAt π s y ↑t))
        (π.at (↑t) (histAt π s y ↑t))) * hbr
  simp only [key]
  unfold EE
  simp only [hm]
  rw [Fintype.sum_bool]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  unfold JJ
  ring


include hM hμ0 hsig hα hπ in
lemma claim_rec : ∀ k t, t + k = T →
    (1/2) ^ k * ∑ s, ∑ y, JH M μ0 sig α π t s y *
        Wk M μ0 sig α π k t (histAt π s y t) =
      ∑ t' : Fin T, if t ≤ (t' : ℕ) then EE M μ0 sig α π t' else 0 := by
  intro k
  induction k with
  | zero =>
    intro t htk
    simp only [Wk, mul_zero, Finset.sum_const_zero]
    symm
    apply Finset.sum_eq_zero
    intro t' _
    rw [if_neg]
    have := t'.isLt
    omega
  | succ k ih =>
    intro t htk
    have htT : t < T := by omega
    have IH := ih (t + 1) (by omega)
    -- unfold one step of the recursion
    have hW : ∀ s y, Wk M μ0 sig α π (k + 1) t (histAt π s y t) =
        eS M μ0 sig α π t s y + ∑ c, prPath M μ0 sig α π t s y c *
          Wk M μ0 sig α π k (t + 1) ((histAt π s y t).snoc (π.at t (histAt π s y t), c)) := by
      intro s y; rfl
    have hflip : ∀ s, ∑ y, JH M μ0 sig α π t s y * ∑ c, prPath M μ0 sig α π t s y c *
          Wk M μ0 sig α π k (t + 1) ((histAt π s y t).snoc (π.at t (histAt π s y t), c)) =
        2 * ∑ y, JH M μ0 sig α π (t + 1) s y * Wk M μ0 sig α π k (t + 1) (histAt π s y (t + 1)) := by
      intro s
      have hf := flip2 (⟨t, htT⟩ : Fin T) (fun y c => JH M μ0 sig α π t s y *
          (prPath M μ0 sig α π t s y c *
            Wk M μ0 sig α π k (t + 1) ((histAt π s y t).snoc (π.at t (histAt π s y t), c))))
        (by
          intro c y y' hyy
          have hh : histAt π s y t = histAt π s y' t := histAt_dep π s y y' t hyy
          have hJ : JH M μ0 sig α π t s y = JH M μ0 sig α π t s y' := by
            unfold JH JJ
            rw [PP_dep M α π true s t y y' hyy, PP_dep M α π false s t y y' hyy]
          simp only [prPath, hh, hJ])
      simp only [Finset.mul_sum]
      simp only [Finset.mul_sum] at hf
      rw [hf]
      apply Finset.sum_congr rfl
      intro y _
      have hy : y ⟨t, htT⟩ = yAt y t := by simp [yAt, htT]
      rw [hy, JH_succ M hM μ0 hμ0 sig hsig α hα π hπ t htT s y]
      have hh : histAt π s y (t + 1) = (histAt π s y t).snoc (π.at t (histAt π s y t), yAt y t) := rfl
      rw [hh]
      ring
    have hEE := EE_eq M hM μ0 hμ0 sig hsig α hα π hπ ⟨t, htT⟩
    simp only at hEE
    rw [show T - t = k + 1 by omega] at hEE
    have hsplit : ∀ t' : Fin T, (if t ≤ (t' : ℕ) then EE M μ0 sig α π t' else 0) =
        (if t' = ⟨t, htT⟩ then EE M μ0 sig α π t' else 0) +
          (if t + 1 ≤ (t' : ℕ) then EE M μ0 sig α π t' else 0) := by
      intro t'
      by_cases h1 : t' = ⟨t, htT⟩
      · subst h1; simp
      · have : (t' : ℕ) ≠ t := fun h => h1 (Fin.ext h)
        by_cases h2 : t + 1 ≤ (t' : ℕ)
        · simp [h1, h2, show t ≤ (t' : ℕ) by omega]
        · simp [h1, h2, show ¬ (t ≤ (t' : ℕ)) by omega]
    rw [Finset.sum_congr rfl (fun t' _ => hsplit t'), Finset.sum_add_distrib, Finset.sum_ite_eq',
      if_pos (Finset.mem_univ _), ← IH, hEE]
    simp only [hW, mul_add, Finset.sum_add_distrib]
    simp only [hflip]
    have h2 : ∑ s, 2 * ∑ y, JH M μ0 sig α π (t + 1) s y *
        Wk M μ0 sig α π k (t + 1) (histAt π s y (t + 1)) =
        2 * ∑ s, ∑ y, JH M μ0 sig α π (t + 1) s y *
          Wk M μ0 sig α π k (t + 1) (histAt π s y (t + 1)) := by
      rw [Finset.mul_sum]
    rw [h2, pow_succ]
    ring

include hM hμ0 hsig hα hπ in
/-- The payoff of any policy with myopic pricing is the signal-average of the recursive
continuation value at the initial history. -/
lemma surplusT_eq_Wk :
    surplusT M μ0 sig α π = ∑ s, (μ0 * sig true s + (1 - μ0) * sig false s) *
      Wk M μ0 sig α π T 0 (s, fun i => i.elim0) := by
  have hc := claim_rec M hM μ0 hμ0 sig hsig α hα π hπ T 0 (by omega)
  simp only [zero_le, if_true] at hc
  have hJ0 : ∀ s y, JH M μ0 sig α π 0 s y = μ0 * sig true s + (1 - μ0) * sig false s := by
    intro s y
    simp [JH, JJ, PP_zero, prior]
  have hh0 : ∀ s y, histAt π s y 0 = (s, fun i => i.elim0) := fun _ _ => rfl
  simp only [hJ0, hh0, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hc
  have hST : surplusT M μ0 sig α π = ∑ t : Fin T, EE M μ0 sig α π t := by
    unfold surplusT ConfoundPromo.LongRun.expect condExpect pathSurplus EE
    simp only [Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    exact Finset.sum_comm
  rw [hST, ← hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [← mul_assoc, ← mul_assoc, ← mul_pow]
  norm_num

end ValueRep

/-! ## The belief-based dynamic program (Lemma 1) -/

/-- one-period value of action `w` at belief `μ` with continuation value `V` -/
noncomputable def Qv (M : Market) (V : ℝ → ℝ) (μ : ℝ) (w : ℝ × ℝ × ℝ) : ℝ :=
  SSf M μ w.1 w.2.1 w.2.2 + ∑ c : Bool, pr M μ w.2.1 w.2.2 w.1 c *
    V (bayes μ (likelihood M true w.2.1 w.1 c) (likelihood M false w.2.2 w.1 c))

/-- valid single-price myopic choice -/
def MyoF (M : Market) (μ : ℝ) (w : ℝ × ℝ × ℝ) : Prop :=
  IsValidRule (rule w) ∧ IsMyopicChoice M μ (rule w) w.1

open Classical in
/-- fallback choice -/
noncomputable def fb (M : Market) (μ : ℝ) : ℝ × ℝ × ℝ :=
  if h : ∃ w, MyoF M μ w then h.choose else (0, 0, 0)

lemma rule_valid_of (w : ℝ × ℝ × ℝ) (h1 : w.2.1 ∈ Set.Icc (0:ℝ) 1) (h2 : w.2.2 ∈ Set.Icc (0:ℝ) 1) :
    IsValidRule (rule w) := by
  intro q b
  simp only [rule]
  split_ifs
  · exact h1
  · exact h2
  · exact ⟨le_refl _, zero_le_one⟩

lemma fb_valid (M : Market) (μ : ℝ) : IsValidRule (rule (fb M μ)) := by
  unfold fb
  split_ifs with h
  · exact h.choose_spec.1
  · exact rule_valid_of _ ⟨le_refl _, zero_le_one⟩ ⟨le_refl _, zero_le_one⟩

lemma fb_myo (M : Market) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1) :
    MyoF M μ (fb M μ) := by
  unfold fb
  split_ifs with h
  · exact h.choose_spec
  · exfalso
    obtain ⟨w, hv, hmy, _⟩ := exists_feas M hM μ hμ
    exact h ⟨w, hv, hmy⟩

section DP

variable (M : Market) {n T : ℕ} (μ0 : ℝ) (sig : Signal n) (α : Promo n T) (π : Pricing n T)

/-- the single-price action used by the original policy at the period-`t` history of a path -/
noncomputable def act (t : ℕ) (sy : Fin n × (Fin T → Bool)) : ℝ × ℝ × ℝ :=
  (π.at t (histAt π sy.1 sy.2 t), α.at t (π.at t (histAt π sy.1 sy.2 t)) true (histAt π sy.1 sy.2 t),
    α.at t (π.at t (histAt π sy.1 sy.2 t)) false (histAt π sy.1 sy.2 t))

open Classical in
/-- candidate actions at period `t` and belief `μ` -/
noncomputable def Cands (t : ℕ) (μ : ℝ) : Finset (ℝ × ℝ × ℝ) :=
  (Finset.univ.filter (fun sy : Fin n × (Fin T → Bool) =>
    belief M μ0 sig α t (histAt π sy.1 sy.2 t) = μ)).image (act α π t)

open Classical in
/-- the decision at period `t` and belief `μ` for continuation value `V` -/
noncomputable def Dec (V : ℝ → ℝ) (t : ℕ) (μ : ℝ) : ℝ × ℝ × ℝ :=
  if h : (Cands M μ0 sig α π t μ).Nonempty then
    (Finset.exists_max_image (Cands M μ0 sig α π t μ) (Qv M V μ) h).choose
  else fb M μ

/-- the value with `k` periods remaining -/
noncomputable def Val : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun μ => Qv M (Val k) μ (Dec M μ0 sig α π (Val k) (T - (k + 1)) μ)

lemma Dec_mem (V : ℝ → ℝ) (t : ℕ) (μ : ℝ) (h : (Cands M μ0 sig α π t μ).Nonempty) :
    Dec M μ0 sig α π V t μ ∈ Cands M μ0 sig α π t μ ∧
      ∀ w ∈ Cands M μ0 sig α π t μ, Qv M V μ w ≤ Qv M V μ (Dec M μ0 sig α π V t μ) := by
  unfold Dec
  rw [dif_pos h]
  exact (Finset.exists_max_image (Cands M μ0 sig α π t μ) (Qv M V μ) h).choose_spec

variable (hα : α.IsValid)

include hα in
lemma Dec_valid (V : ℝ → ℝ) (t : ℕ) (μ : ℝ) : IsValidRule (rule (Dec M μ0 sig α π V t μ)) := by
  by_cases h : (Cands M μ0 sig α π t μ).Nonempty
  · obtain ⟨hm, _⟩ := Dec_mem M μ0 sig α π V t μ h
    unfold Cands at hm
    obtain ⟨sy, _, hsy⟩ := Finset.mem_image.mp hm
    rw [← hsy]
    exact rule_valid_of _ (promo_mem α hα _ _ _ _) (promo_mem α hα _ _ _ _)
  · unfold Dec
    rw [dif_neg h]
    exact fb_valid M μ

variable (hM : M.Standing) (hμ0 : μ0 ∈ Set.Icc (0:ℝ) 1) (hsig : sig.IsValid)
  (hπ : IsMyopic M μ0 sig α π)

include hM hα hπ hμ0 hsig in
lemma Dec_myo (V : ℝ → ℝ) (t : ℕ) (ht : t < T) (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1) :
    MyoF M μ (Dec M μ0 sig α π V t μ) := by
  by_cases h : (Cands M μ0 sig α π t μ).Nonempty
  · obtain ⟨hm, _⟩ := Dec_mem M μ0 sig α π V t μ h
    unfold Cands at hm
    obtain ⟨sy, hsyf, hsy⟩ := Finset.mem_image.mp hm
    rw [← hsy]
    have hbel : belief M μ0 sig α t (histAt π sy.1 sy.2 t) = μ := (Finset.mem_filter.mp hsyf).2
    refine ⟨rule_valid_of _ (promo_mem α hα _ _ _ _) (promo_mem α hα _ _ _ _), ?_⟩
    have hin := histAt_inPrice M μ0 sig α π hπ sy.1 sy.2 t ht.le
    have hmy := hπ ⟨t, ht⟩ _ hin
    simp only at hmy
    rw [hbel] at hmy
    have hav : IsValidRule (fun q b => α ⟨t, ht⟩ q b (histAt π sy.1 sy.2 t)) :=
      fun q b => hα _ _ _ _
    have hsp := single_price_myopic M hM μ hμ _ hav _ hmy
    have e1 : π.at t (histAt π sy.1 sy.2 t) = π ⟨t, ht⟩ (histAt π sy.1 sy.2 t) := by
      simp [Pricing.at, ht]
    have e2 : ∀ q b, α.at t q b (histAt π sy.1 sy.2 t) = α ⟨t, ht⟩ q b (histAt π sy.1 sy.2 t) := by
      intro q b; simp [Promo.at, ht]
    simp only [act, e1, e2]
    exact hsp
  · unfold Dec
    rw [dif_neg h]
    exact fb_myo M hM μ hμ

include hM hα hπ hμ0 hsig in
/-- The dynamic program dominates the original continuation values (proof of Lemma 1). -/
lemma Wk_le_Val : ∀ k t, t + k = T → ∀ (s : Fin n) (y : Fin T → Bool),
    Wk M μ0 sig α π k t (histAt π s y t) ≤
      Val M μ0 sig α π k (belief M μ0 sig α t (histAt π s y t)) := by
  intro k
  induction k with
  | zero => intro t _ s y; simp [Wk, Val]
  | succ k ih =>
    intro t htk s y
    have htT : t < T := by omega
    set h := histAt π s y t with hh
    set μ := belief M μ0 sig α t h with hμ
    set p := π.at t h with hp
    set w := act α π t (s, y) with hw
    have hμm : μ ∈ Set.Icc (0:ℝ) 1 :=
      belief_mem M hM μ0 hμ0 sig hsig α hα t h (histAt_inPrice M μ0 sig α π hπ s y t htT.le)
    have hpm : p ∈ M.price := price_mem M μ0 sig α π hπ s y t htT
    have hwm : w ∈ Cands M μ0 sig α π t μ := by
      unfold Cands
      exact Finset.mem_image.mpr ⟨(s, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
    have hne : (Cands M μ0 sig α π t μ).Nonempty := ⟨w, hwm⟩
    obtain ⟨_, hmax⟩ := Dec_mem M μ0 sig α π (Val M μ0 sig α π k) t μ hne
    have hVal : Val M μ0 sig α π (k + 1) μ =
        Qv M (Val M μ0 sig α π k) μ (Dec M μ0 sig α π (Val M μ0 sig α π k) t μ) := by
      show Qv M (Val M μ0 sig α π k) μ (Dec M μ0 sig α π (Val M μ0 sig α π k) (T - (k + 1)) μ) = _
      rw [show T - (k + 1) = t by omega]
    rw [hVal]
    refine le_trans ?_ (hmax w hwm)
    -- one step of the original recursion
    have hW : Wk M μ0 sig α π (k + 1) t h =
        expSurplus M μ (fun q b => α.at t q b h) p + ∑ c, pr M μ (α.at t p true h) (α.at t p false h) p c *
          Wk M μ0 sig α π k (t + 1) (h.snoc (p, c)) := rfl
    rw [hW]
    unfold Qv
    have e1 : expSurplus M μ (fun q b => α.at t q b h) p = SSf M μ w.1 w.2.1 w.2.2 := rfl
    rw [e1]
    refine add_le_add le_rfl ?_
    apply Finset.sum_le_sum
    intro c _
    have hprn : 0 ≤ pr M μ (α.at t p true h) (α.at t p false h) p c :=
      pr_nonneg M hM μ _ _ p hμm (promo_mem α hα _ _ _ _) (promo_mem α hα _ _ _ _) hpm c
    have e2 : pr M μ w.2.1 w.2.2 w.1 c = pr M μ (α.at t p true h) (α.at t p false h) p c := rfl
    rw [e2]
    apply mul_le_mul_of_nonneg_left _ hprn
    -- the successor history is a path history
    set y' : Fin T → Bool := Function.update y ⟨t, htT⟩ c with hy'
    have hagree : ∀ i : Fin T, (i : ℕ) < t → y i = y' i := by
      intro i hi
      have : i ≠ ⟨t, htT⟩ := fun e => by rw [e] at hi; exact lt_irrefl _ hi
      simp [hy', Function.update_of_ne this]
    have hht : histAt π s y' t = h := (histAt_dep π s y y' t hagree).symm
    have hyt : yAt y' t = c := by simp [yAt, htT, hy']
    have hsucc : h.snoc (p, c) = histAt π s y' (t + 1) := by
      show h.snoc (p, c) = (histAt π s y' t).snoc (π.at t (histAt π s y' t), yAt y' t)
      rw [hht, hyt]
    have IH := ih (t + 1) (by omega) s y'
    rw [← hsucc] at IH
    refine le_trans IH (le_of_eq ?_)
    congr 1
    rw [hsucc, belief_succ_path]
    simp only [lik, hht, hyt]
    rfl

end DP

/-! ## The new belief-based single-price policy -/

lemma expSurplus_rule' (M : Market) (μ : ℝ) (w : ℝ × ℝ × ℝ) :
    expSurplus M μ (rule w) w.1 = SSf M μ w.1 w.2.1 w.2.2 := by
  simp [expSurplus, rule, SSf]

/-- beliefs under the belief-based policy applying `rule (DD t μ)` at period `t`, belief `μ` -/
noncomputable def beliefD (M : Market) {n' : ℕ} (T : ℕ) (μ0 : ℝ) (sig' : Signal n')
    (DD : ℕ → ℝ → ℝ × ℝ × ℝ) : (t : ℕ) → SHist n' t → ℝ
  | 0, h => bayes μ0 (sig' true h.1) (sig' false h.1)
  | t + 1, h =>
      bayes (beliefD M T μ0 sig' DD t h.init)
        (likelihood M true (if t < T then rule (DD t (beliefD M T μ0 sig' DD t h.init)) h.last.1 true
          else 0) h.last.1 h.last.2)
        (likelihood M false (if t < T then rule (DD t (beliefD M T μ0 sig' DD t h.init)) h.last.1 false
          else 0) h.last.1 h.last.2)

/-- the new promotion policy -/
noncomputable def newα (M : Market) {n' : ℕ} (T : ℕ) (μ0 : ℝ) (sig' : Signal n')
    (DD : ℕ → ℝ → ℝ × ℝ × ℝ) : Promo n' T :=
  fun t q b h => rule (DD t (beliefD M T μ0 sig' DD t h)) q b

/-- the new pricing policy -/
noncomputable def newπ (M : Market) {n' : ℕ} (T : ℕ) (μ0 : ℝ) (sig' : Signal n')
    (DD : ℕ → ℝ → ℝ × ℝ × ℝ) : Pricing n' T :=
  fun t h => (DD t (beliefD M T μ0 sig' DD t h)).1

lemma belief_eq_beliefD (M : Market) {n' : ℕ} (T : ℕ) (μ0 : ℝ) (sig' : Signal n')
    (DD : ℕ → ℝ → ℝ × ℝ × ℝ) : ∀ (t : ℕ) (h : SHist n' t),
      belief M μ0 sig' (newα M T μ0 sig' DD) t h = beliefD M T μ0 sig' DD t h := by
  intro t
  induction t with
  | zero => intro h; simp [belief, beliefD]
  | succ t ih =>
    intro h
    rw [belief, beliefD, ih]
    simp only [Promo.at, newα, dite_eq_ite]

lemma newα_at (M : Market) {n' : ℕ} (T : ℕ) (μ0 : ℝ) (sig' : Signal n')
    (DD : ℕ → ℝ → ℝ × ℝ × ℝ) (t : ℕ) (ht : t < T) (q : ℝ) (b : Bool) (h : SHist n' t) :
    (newα M T μ0 sig' DD).at t q b h = rule (DD t (beliefD M T μ0 sig' DD t h)) q b := by
  simp [Promo.at, ht, newα]

lemma newπ_at (M : Market) {n' : ℕ} (T : ℕ) (μ0 : ℝ) (sig' : Signal n')
    (DD : ℕ → ℝ → ℝ × ℝ × ℝ) (t : ℕ) (ht : t < T) (h : SHist n' t) :
    (newπ M T μ0 sig' DD).at t h = (DD t (beliefD M T μ0 sig' DD t h)).1 := by
  simp [Pricing.at, ht, newπ]

section NewPolicy

variable (M : Market) {n T : ℕ} (μ0 : ℝ) (sig : Signal n) (α : Promo n T) (π : Pricing n T)

/-- the decision rule of the dynamic program -/
noncomputable def DDp (t : ℕ) (μ : ℝ) : ℝ × ℝ × ℝ :=
  Dec M μ0 sig α π (Val M μ0 sig α π (T - t - 1)) t μ

lemma Wk_new {n' : ℕ} (sig' : Signal n') : ∀ k t, t + k = T → ∀ h : SHist n' t,
    Wk M μ0 sig' (newα M T μ0 sig' (DDp M μ0 sig α π)) (newπ M T μ0 sig' (DDp M μ0 sig α π)) k t h =
      Val M μ0 sig α π k (beliefD M T μ0 sig' (DDp M μ0 sig α π) t h) := by
  intro k
  induction k with
  | zero => intro t _ h; simp [Wk, Val]
  | succ k ih =>
    intro t htk h
    have htT : t < T := by omega
    set μ := beliefD M T μ0 sig' (DDp M μ0 sig α π) t h with hμ
    set w := DDp M μ0 sig α π t μ with hw
    have hVal : Val M μ0 sig α π (k + 1) μ = Qv M (Val M μ0 sig α π k) μ w := by
      show Qv M (Val M μ0 sig α π k) μ (Dec M μ0 sig α π (Val M μ0 sig α π k) (T - (k + 1)) μ) = _
      rw [hw, DDp, show T - (k + 1) = t by omega, show T - t - 1 = k by omega]
    rw [hVal]
    show expSurplus M (belief M μ0 sig' (newα M T μ0 sig' (DDp M μ0 sig α π)) t h)
        (fun q b => (newα M T μ0 sig' (DDp M μ0 sig α π)).at t q b h)
        ((newπ M T μ0 sig' (DDp M μ0 sig α π)).at t h) +
      ∑ c, pr M (belief M μ0 sig' (newα M T μ0 sig' (DDp M μ0 sig α π)) t h)
          ((newα M T μ0 sig' (DDp M μ0 sig α π)).at t ((newπ M T μ0 sig' (DDp M μ0 sig α π)).at t h) true h)
          ((newα M T μ0 sig' (DDp M μ0 sig α π)).at t ((newπ M T μ0 sig' (DDp M μ0 sig α π)).at t h) false h)
          ((newπ M T μ0 sig' (DDp M μ0 sig α π)).at t h) c *
        Wk M μ0 sig' (newα M T μ0 sig' (DDp M μ0 sig α π)) (newπ M T μ0 sig' (DDp M μ0 sig α π)) k (t + 1)
          (h.snoc ((newπ M T μ0 sig' (DDp M μ0 sig α π)).at t h, c)) = _
    simp only [belief_eq_beliefD, newπ_at M T μ0 sig' _ t htT, newα_at M T μ0 sig' _ t htT, ← hμ, ← hw]
    have hr1 : rule w w.1 true = w.2.1 := by simp [rule]
    have hr2 : rule w w.1 false = w.2.2 := by simp [rule]
    rw [hr1, hr2]
    unfold Qv
    rw [expSurplus_rule']
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    rw [ih (t + 1) (by omega)]
    congr 2
    rw [beliefD]
    have hi : (h.snoc (w.1, c)).init = h := by simp [SHist.snoc, SHist.init]
    have hl : (h.snoc (w.1, c)).last = (w.1, c) := by simp [SHist.snoc, SHist.last]
    simp only [hi, hl, if_pos htT, ← hμ, ← hw, hr1, hr2]

variable (hM : M.Standing) (hμ0 : μ0 ∈ Set.Icc (0:ℝ) 1) (hsig : sig.IsValid) (hα : α.IsValid)
  (hπ : IsMyopic M μ0 sig α π)

include hα in
lemma newα_valid {n' : ℕ} (sig' : Signal n') : (newα M T μ0 sig' (DDp M μ0 sig α π)).IsValid := by
  intro t q b h
  exact Dec_valid M μ0 sig α π hα _ _ _ q b

include hM hα hπ hμ0 hsig in
lemma new_props {n' : ℕ} (sig' : Signal n') (hsig' : sig'.IsValid) :
    IsSinglePrice M (newα M T μ0 sig' (DDp M μ0 sig α π)) ∧
    IsBeliefBased M μ0 sig' (newα M T μ0 sig' (DDp M μ0 sig α π)) ∧
    IsMyopic M μ0 sig' (newα M T μ0 sig' (DDp M μ0 sig α π)) (newπ M T μ0 sig' (DDp M μ0 sig α π)) := by
  have hv := newα_valid M μ0 sig α π hα sig'
  have hmyo : ∀ (t : Fin T) (h : SHist n' t), h.InPrice M →
      MyoF M (beliefD M T μ0 sig' (DDp M μ0 sig α π) t h)
        (DDp M μ0 sig α π t (beliefD M T μ0 sig' (DDp M μ0 sig α π) t h)) := by
    intro t h hh
    have hb := belief_mem M hM μ0 hμ0 sig' hsig' _ hv t h hh
    rw [belief_eq_beliefD] at hb
    exact Dec_myo M μ0 sig α π hα hM hμ0 hsig hπ _ t t.isLt _ hb
  refine ⟨?_, ?_, ?_⟩
  · intro t h hh
    refine ⟨_, (hmyo t h hh).2.1, ?_⟩
    intro q _ hq b
    simp [newα, rule, hq]
  · intro t h h' _ _ heq q _ b
    rw [belief_eq_beliefD, belief_eq_beliefD] at heq
    simp only [newα]
    rw [heq]
  · intro t h hh
    rw [belief_eq_beliefD]
    exact (hmyo t h hh).2

end NewPolicy

/-! ## Reduction to two signals (Proposition 1, step 2) -/

/-- A finite convex combination is dominated by a two-point split of the same barycenter. -/
lemma fc {ι : Type} [Fintype ι] (P x : ι → ℝ) (f : ℝ → ℝ) (μ0 : ℝ) (hP : ∀ i, 0 ≤ P i)
    (hsum : ∑ i, P i = 1) (hx : ∀ i, x i ∈ Set.Icc (0:ℝ) 1) (hbar : ∑ i, P i * x i = μ0) :
    ∃ l x1 x2 : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ x1 ∈ Set.Icc (0:ℝ) 1 ∧ x2 ∈ Set.Icc (0:ℝ) 1 ∧
      l * x1 + (1 - l) * x2 = μ0 ∧ ∑ i, P i * f (x i) ≤ l * f x1 + (1 - l) * f x2 := by
  classical
  have hdev : ∑ i, P i * (x i - μ0) = 0 := by
    have : ∑ i, P i * (x i - μ0) = ∑ i, P i * x i - μ0 * ∑ i, P i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [this, hbar, hsum]; ring
  have hex : ∃ i, 0 < P i := by
    by_contra h
    push_neg at h
    have : ∑ i, P i = 0 := Finset.sum_eq_zero (fun i _ => le_antisymm (h i) (hP i))
    linarith
  -- a left point and a right point with positive weight
  have hleft : ∃ i, 0 < P i ∧ x i ≤ μ0 := by
    by_contra h
    push_neg at h
    obtain ⟨i0, hi0⟩ := hex
    have hpos : 0 < ∑ i, P i * (x i - μ0) := by
      apply Finset.sum_pos'
      · intro i _
        rcases eq_or_lt_of_le (hP i) with h0 | h0
        · rw [← h0]; simp
        · exact mul_nonneg h0.le (by linarith [h i h0])
      · exact ⟨i0, Finset.mem_univ _, mul_pos hi0 (by linarith [h i0 hi0])⟩
    linarith
  have hright : ∃ j, 0 < P j ∧ μ0 ≤ x j := by
    by_contra h
    push_neg at h
    obtain ⟨i0, hi0⟩ := hex
    have hneg : ∑ i, P i * (x i - μ0) < 0 := by
      apply Finset.sum_neg'
      · intro i _
        rcases eq_or_lt_of_le (hP i) with h0 | h0
        · rw [← h0]; simp
        · exact mul_nonpos_of_nonneg_of_nonpos h0.le (by linarith [h i h0])
      · exact ⟨i0, Finset.mem_univ _, mul_neg_of_pos_of_neg hi0 (by linarith [h i0 hi0])⟩
    linarith
  -- the candidate pairs and their split values
  set Pairs : Finset (ι × ι) := Finset.univ.filter
    (fun ij : ι × ι => 0 < P ij.1 ∧ 0 < P ij.2 ∧ x ij.1 ≤ μ0 ∧ μ0 ≤ x ij.2) with hPairs
  set g : ι × ι → ℝ := fun ij => if x ij.1 = x ij.2 then f (x ij.1) else
    ((x ij.2 - μ0) * f (x ij.1) + (μ0 - x ij.1) * f (x ij.2)) / (x ij.2 - x ij.1) with hg
  obtain ⟨i1, hi1, hxi1⟩ := hleft
  obtain ⟨j1, hj1, hxj1⟩ := hright
  have hne : Pairs.Nonempty :=
    ⟨(i1, j1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi1, hj1, hxi1, hxj1⟩⟩
  obtain ⟨ij, hij, hmax⟩ := Finset.exists_max_image Pairs g hne
  obtain ⟨_, hPi, hPj, hxi, hxj⟩ := Finset.mem_filter.mp hij
  set V := g ij with hV
  -- the pair inequality and the midpoint inequality
  have hpair : ∀ i j, 0 < P i → 0 < P j → x i < μ0 → μ0 < x j →
      (x j - μ0) * f (x i) + (μ0 - x i) * f (x j) ≤ V * (x j - x i) := by
    intro i j hi hj hxi' hxj'
    have hm := hmax (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hj, hxi'.le, hxj'.le⟩)
    have hne' : x i ≠ x j := by intro h; linarith
    simp only [hg, if_neg hne'] at hm
    rw [div_le_iff₀ (by linarith)] at hm
    exact hm
  have hmid : ∀ i, 0 < P i → x i = μ0 → f (x i) ≤ V := by
    intro i hi hxi'
    have hm := hmax (i, i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hi, hxi'.le, hxi'.ge⟩)
    simp only [hg, if_pos rfl] at hm
    exact hm
  -- the slope of a supporting line
  set R : Finset ι := Finset.univ.filter (fun j => 0 < P j ∧ μ0 < x j) with hR
  set k : ℝ := if hRn : R.Nonempty then
      (R.image (fun j => (f (x j) - V) / (x j - μ0))).max' (Finset.image_nonempty.mpr hRn)
    else 0 with hk
  have hbound : ∀ i, P i * f (x i) ≤ P i * (V + k * (x i - μ0)) := by
    intro i
    rcases eq_or_lt_of_le (hP i) with h0 | h0
    · rw [← h0]; simp
    apply mul_le_mul_of_nonneg_left _ h0.le
    rcases lt_trichotomy (x i) μ0 with hlt | heq | hgt
    · -- a left point: some right point exists
      have hRn : R.Nonempty := by
        by_contra hRe
        rw [Finset.not_nonempty_iff_eq_empty] at hRe
        have hneg : ∑ j, P j * (x j - μ0) < 0 := by
          apply Finset.sum_neg'
          · intro j _
            rcases eq_or_lt_of_le (hP j) with h0' | h0'
            · rw [← h0']; simp
            · have : ¬ (0 < P j ∧ μ0 < x j) := by
                intro hc
                have : j ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
                rw [hRe] at this; simp at this
              push_neg at this
              exact mul_nonpos_of_nonneg_of_nonpos h0'.le (by linarith [this h0'])
          · exact ⟨i, Finset.mem_univ _, mul_neg_of_pos_of_neg h0 (by linarith)⟩
        linarith
      have hk' : k ≤ (V - f (x i)) / (μ0 - x i) := by
        rw [hk, dif_pos hRn]
        apply Finset.max'_le
        intro e he
        obtain ⟨j, hjR, rfl⟩ := Finset.mem_image.mp he
        obtain ⟨_, hPj', hxj'⟩ := Finset.mem_filter.mp hjR
        have := hpair i j h0 hPj' hlt hxj'
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
      rw [le_div_iff₀ (by linarith)] at hk'
      nlinarith
    · rw [heq]; simp only [sub_self, mul_zero, add_zero]; rw [← heq]; exact hmid i h0 heq
    · have hiR : i ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0, hgt⟩
      have hRn : R.Nonempty := ⟨i, hiR⟩
      have hk' : (f (x i) - V) / (x i - μ0) ≤ k := by
        rw [hk, dif_pos hRn]
        apply Finset.le_max'
        exact Finset.mem_image.mpr ⟨i, hiR, rfl⟩
      rw [div_le_iff₀ (by linarith)] at hk'
      nlinarith
  have htot : ∑ i, P i * f (x i) ≤ V := by
    calc ∑ i, P i * f (x i) ≤ ∑ i, P i * (V + k * (x i - μ0)) := Finset.sum_le_sum (fun i _ => hbound i)
      _ = V * ∑ i, P i + k * ∑ i, P i * (x i - μ0) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro i _; ring
      _ = V := by rw [hsum, hdev]; ring
  -- realize `V` by a two-point split
  by_cases hEq : x ij.1 = x ij.2
  · have hx1 : x ij.1 = μ0 := le_antisymm hxi (hEq ▸ hxj)
    refine ⟨1, x ij.1, x ij.2, zero_le_one, le_refl _, hx ij.1, hx ij.2, ?_, ?_⟩
    · rw [hx1]; ring
    · have : V = f (x ij.1) := by simp only [hV, hg, if_pos hEq]
      rw [← this]; linarith
  · have hlt : x ij.1 < x ij.2 := lt_of_le_of_ne (le_trans hxi hxj) hEq
    have hd : 0 < x ij.2 - x ij.1 := by linarith
    refine ⟨(x ij.2 - μ0) / (x ij.2 - x ij.1), x ij.1, x ij.2, div_nonneg (by linarith) hd.le,
      by rw [div_le_one hd]; linarith, hx ij.1, hx ij.2, ?_, ?_⟩
    · field_simp; ring
    · have : V = (x ij.2 - μ0) / (x ij.2 - x ij.1) * f (x ij.1) +
          (1 - (x ij.2 - μ0) / (x ij.2 - x ij.1)) * f (x ij.2) := by
        simp only [hV, hg, if_neg hEq]
        field_simp
        ring
      rw [← this]; exact htot

/-- A two-point split of the prior is generated by a two-signal mechanism. -/
lemma realize (f : ℝ → ℝ) (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0:ℝ) 1) (l x1 x2 : ℝ) (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) (hx1 : x1 ∈ Set.Icc (0:ℝ) 1) (hx2 : x2 ∈ Set.Icc (0:ℝ) 1)
    (hsum : l * x1 + (1 - l) * x2 = μ0) :
    ∃ sig : Signal 2, sig.IsValid ∧
      ∑ s, (μ0 * sig true s + (1 - μ0) * sig false s) * f (bayes μ0 (sig true s) (sig false s)) =
        l * f x1 + (1 - l) * f x2 := by
  obtain ⟨h0, h1⟩ := hμ0
  obtain ⟨hx10, hx11⟩ := hx1
  obtain ⟨hx20, hx21⟩ := hx2
  have hl1' : 0 ≤ 1 - l := by linarith
  -- the generic term computation
  have term : ∀ lH lL w x : ℝ, μ0 * lH + (1 - μ0) * lL = w → 0 ≤ w → (0 < w → μ0 * lH / w = x) →
      (μ0 * lH + (1 - μ0) * lL) * f (bayes μ0 lH lL) = w * f x := by
    intro lH lL w x hw hw0 hpost
    rw [hw]
    rcases eq_or_lt_of_le hw0 with h | h
    · rw [← h]; ring
    · have hb : bayes μ0 lH lL = x := by
        unfold bayes
        rw [hw, if_neg h.ne']
        exact hpost h
      rw [hb]
  by_cases hend : μ0 * (1 - μ0) = 0
  · -- the prior is degenerate: both posteriors coincide with it
    have hval : l * f x1 + (1 - l) * f x2 = f μ0 := by
      rcases mul_eq_zero.mp hend with h | h
      · have e1 : l * x1 = 0 := by nlinarith [mul_nonneg hl0 hx10, mul_nonneg hl1' hx20]
        have e2 : (1 - l) * x2 = 0 := by nlinarith [mul_nonneg hl0 hx10, mul_nonneg hl1' hx20]
        have t1 : l * f x1 = l * f μ0 := by
          rcases eq_or_lt_of_le hl0 with hl | hl
          · rw [← hl]; ring
          · rw [(mul_eq_zero.mp e1).resolve_left hl.ne', h]
        have t2 : (1 - l) * f x2 = (1 - l) * f μ0 := by
          rcases eq_or_lt_of_le hl1' with hl | hl
          · rw [← hl]; ring
          · rw [(mul_eq_zero.mp e2).resolve_left hl.ne', h]
        rw [t1, t2]; ring
      · have hμ1 : μ0 = 1 := by linarith
        have e1 : l * (1 - x1) = 0 := by
          nlinarith [mul_nonneg hl0 (by linarith : (0:ℝ) ≤ 1 - x1),
            mul_nonneg hl1' (by linarith : (0:ℝ) ≤ 1 - x2)]
        have e2 : (1 - l) * (1 - x2) = 0 := by
          nlinarith [mul_nonneg hl0 (by linarith : (0:ℝ) ≤ 1 - x1),
            mul_nonneg hl1' (by linarith : (0:ℝ) ≤ 1 - x2)]
        have t1 : l * f x1 = l * f μ0 := by
          rcases eq_or_lt_of_le hl0 with hl | hl
          · rw [← hl]; ring
          · have := (mul_eq_zero.mp e1).resolve_left hl.ne'
            rw [hμ1, show x1 = 1 by linarith]
        have t2 : (1 - l) * f x2 = (1 - l) * f μ0 := by
          rcases eq_or_lt_of_le hl1' with hl | hl
          · rw [← hl]; ring
          · have := (mul_eq_zero.mp e2).resolve_left hl.ne'
            rw [hμ1, show x2 = 1 by linarith]
        rw [t1, t2]; ring
    obtain ⟨sig, hsig⟩ : ∃ sig : Signal 2, sig = fun _ s => if s = 0 then 1 else 0 := ⟨_, rfl⟩
    have hv : sig.IsValid := by
      refine ⟨fun b s => ?_, fun b => ?_⟩
      · rw [hsig]; dsimp only; split_ifs <;> norm_num
      · rw [hsig, Fin.sum_univ_two]; simp
    refine ⟨sig, hv, ?_⟩
    rw [Fin.sum_univ_two, hval]
    have s0t : sig true 0 = 1 := by rw [hsig]; simp
    have s0f : sig false 0 = 1 := by rw [hsig]; simp
    have s1t : sig true 1 = 0 := by rw [hsig]; simp
    have s1f : sig false 1 = 0 := by rw [hsig]; simp
    rw [s0t, s0f, s1t, s1f, bayes_same, bayes_same]
    ring
  · have hμ0' : 0 < μ0 := by
      rcases eq_or_lt_of_le h0 with h | h
      · exact absurd (by rw [← h]; ring) hend
      · exact h
    have hμ1' : μ0 < 1 := by
      rcases eq_or_lt_of_le h1 with h | h
      · exact absurd (by rw [h]; ring) hend
      · exact h
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
    rw [term (sig true 0) (sig false 0) l x1 (by rw [s0t, s0f]; field_simp; ring) hl0
      (by intro h; rw [s0t]; field_simp)]
    rw [term (sig true 1) (sig false 1) (1 - l) x2 (by rw [s1t, s1f]; field_simp; ring) hl1'
      (by intro h; rw [s1t]; field_simp)]

end CPSolP1

open CPSolP1

theorem solution (M : Market) (hM : M.Standing) (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0 : ℝ) 1)
    (T n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T)
    (hsig : sig.IsValid) (hα : α.IsValid) (hπ : IsMyopic M μ0 sig α π) :
    ∃ (α' : Promo n T) (π' : Pricing n T), α'.IsValid ∧ IsBeliefBased M μ0 sig α' ∧
      IsMyopic M μ0 sig α' π' ∧ surplusT M μ0 sig α π ≤ surplusT M μ0 sig α' π' := by
  have hA := surplusT_eq_Wk M hM μ0 hμ0 sig hsig α hα π hπ
  obtain ⟨_, hbb, hmy⟩ := new_props M μ0 sig α π hM hμ0 hsig hα hπ sig hsig
  have hv' := newα_valid M μ0 sig α π hα sig
  refine ⟨newα M T μ0 sig (DDp M μ0 sig α π), newπ M T μ0 sig (DDp M μ0 sig α π),
    hv', hbb, hmy, ?_⟩
  have hA' := surplusT_eq_Wk M hM μ0 hμ0 sig hsig _ hv' _ hmy
  rw [hA, hA']
  apply Finset.sum_le_sum
  intro s _
  have hP : 0 ≤ μ0 * sig true s + (1 - μ0) * sig false s :=
    add_nonneg (mul_nonneg hμ0.1 (hsig.1 _ _)) (mul_nonneg (by linarith [hμ0.2]) (hsig.1 _ _))
  apply mul_le_mul_of_nonneg_left _ hP
  have hw := Wk_le_Val M μ0 sig α π hα hM hμ0 hsig hπ T 0 (by omega) s (fun _ => false)
  rw [Wk_new M μ0 sig α π sig T 0 (by omega)]
  exact hw
