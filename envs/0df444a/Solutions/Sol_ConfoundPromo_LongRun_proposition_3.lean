-- Prove2me | solution 1 for ConfoundPromo.LongRun.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:38:58.365999+00:00
-- url     : https://prove2.me/submissions/e274335e-8a16-4c18-8b15-7cce8a3a6499

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

open ConfoundPromo.LongRun
open Finset

namespace CPSolProp3

lemma bayes_same (μ l : ℝ) : bayes μ l l = μ := by
  unfold bayes
  have : μ * l + (1 - μ) * l = l := by ring
  rw [this]
  split_ifs with h
  · rfl
  · field_simp

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

end CPSolProp3

open CPSolProp3

theorem solution (M : Market) (hM : M.Standing) (T : ℕ) (hT : 0 < T)
    (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (α : Promo 1 T) (π : Pricing 1 T), α.IsValid ∧ IsBeliefBased M μ trivialSignal α ∧
      IsSinglePrice M α ∧ IsMyopic M μ trivialSignal α π ∧
      IsConfounding M μ trivialSignal α π := by
  set P := M.price with hP
  have hφL := hM.phiL_pos
  have hφLH := hM.phiL_lt_phiH
  have hφH := hM.phiH_lt_one
  -- confounded revenue
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
  -- strict: q ≠ ps → R q < R ps
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
  -- positivity of rhoC at negative prices
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
  -- the promotion rule
  set aH : ℝ := (M.phiL * M.rho0 ps + (M.phiH - M.phiL) * M.rhoC ps) / (M.phiH * M.rho0 ps)
    with haH
  set a : ℝ → Bool → ℝ := fun q b => if q = ps then (if b then aH else 1) else 0 with ha
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
  have haValid : ∀ q b, a q b ∈ Set.Icc (0:ℝ) 1 := by
    intro q b
    simp only [ha]
    split_ifs
    · exact ⟨haH0, haH1⟩
    · exact ⟨zero_le_one, le_refl _⟩
    · exact ⟨le_refl _, zero_le_one⟩
  have hsale : saleProb M true (a ps true) ps = saleProb M false (a ps false) ps := by
    simp only [ha, if_true, Bool.false_eq_true, if_false, saleProb, Market.phiVal]
    rcases eq_or_lt_of_le (le_trans hc0 hcle) with h0 | h0
    · have hc' : M.rhoC ps = 0 := le_antisymm (h0 ▸ hcle) hc0
      rw [← h0, hc']; ring
    · rw [haH]
      have : M.phiH ≠ 0 := by linarith
      have : M.rho0 ps ≠ 0 := h0.ne'
      field_simp
      ring
  have hrevp : ∀ μ', expRev M μ' a ps = R ps := by
    intro μ'
    simp only [expRev, hR]
    rw [hsale]
    simp only [ha, if_true, Bool.false_eq_true, if_false, saleProb, Market.phiVal]
    ring
  have hrevq : ∀ μ' ∈ Set.Icc (0:ℝ) 1, ∀ q ∈ P, q ≠ ps → expRev M μ' a q < R ps := by
    intro μ' hμ' q hq hne
    have hrev : expRev M μ' a q =
        q * ((μ' * (1 - M.phiH) + (1 - μ') * (1 - M.phiL)) * M.rhoC q) := by
      simp only [expRev, ha, hne, if_false, saleProb, Market.phiVal, if_true,
        Bool.false_eq_true]
      ring
    rw [hrev]
    obtain ⟨h0, h1⟩ := hμ'
    rcases le_or_gt 0 q with hq0 | hq0
    · have hcq := hM.rhoC_nonneg q hq
      have h0q := hM.rhoC_le_rho0 q hq
      have hRq := hstrict q hq hne
      simp only [hR] at hRq
      have hcoef : μ' * (1 - M.phiH) + (1 - μ') * (1 - M.phiL) ≤ 1 - M.phiL := by nlinarith
      have : q * ((μ' * (1 - M.phiH) + (1 - μ') * (1 - M.phiL)) * M.rhoC q) ≤
          q * ((1 - M.phiL) * M.rhoC q) := by
        apply mul_le_mul_of_nonneg_left _ hq0
        exact mul_le_mul_of_nonneg_right hcoef hcq
      have : q * ((1 - M.phiL) * M.rhoC q) ≤ q * (M.phiL * M.rho0 q + (1 - M.phiL) * M.rhoC q) := by
        apply mul_le_mul_of_nonneg_left _ hq0
        nlinarith
      linarith
    · have hcq := hneg q hq hq0
      have hcoef : 0 < μ' * (1 - M.phiH) + (1 - μ') * (1 - M.phiL) := by nlinarith
      have h0P : (0:ℝ) ∈ P := ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩
      have hR0 : R 0 ≤ R ps := hmax h0P
      simp only [hR, zero_mul] at hR0
      simp only [hR]
      have : q * ((μ' * (1 - M.phiH) + (1 - μ') * (1 - M.phiL)) * M.rhoC q) < 0 :=
        mul_neg_of_neg_of_pos hq0 (mul_pos hcoef hcq)
      linarith
  have hmyo : ∀ μ' ∈ Set.Icc (0:ℝ) 1, IsMyopicChoice M μ' a ps := by
    intro μ' hμ'
    refine ⟨hps, ?_, ?_⟩
    · intro q hq
      by_cases hqe : q = ps
      · rw [hqe]
      · rw [hrevp]; exact (hrevq μ' hμ' q hq hqe).le
    · intro q hq heq
      by_cases hqe : q = ps
      · rw [hqe]
      · exfalso
        have := hrevq μ' hμ' q hq hqe
        rw [heq, hrevp] at this
        exact lt_irrefl _ this
  -- policies
  refine ⟨fun _ q b _ => a q b, fun _ _ => ps, ?_, ?_, ?_, ?_, ?_⟩
  · intro t q b h; exact haValid q b
  · intro t h h' _ _ _ q _ b; rfl
  · intro t h _
    refine ⟨ps, hps, ?_⟩
    intro q _ hne b
    simp [ha, hne]
  · intro t h hh
    have hsigv : (trivialSignal).IsValid := by
      refine ⟨fun _ _ => zero_le_one, fun _ => ?_⟩
      simp [trivialSignal]
    have hαv : Promo.IsValid (fun (_ : Fin T) q b (_ : SHist 1 _) => a q b) :=
      fun _ q b _ => haValid q b
    exact hmyo _ (belief_mem M hM μ hμ trivialSignal hsigv _ hαv t h hh)
  · intro b s y _ t
    -- beliefs stay at μ
    have key : ∀ k : ℕ, k ≤ T → belief M μ trivialSignal (fun (_ : Fin T) q b (_ : SHist 1 _) => a q b) k
        (histAt (fun (_ : Fin T) (_ : SHist 1 _) => ps) s y k) = μ := by
      intro k
      induction k with
      | zero =>
        intro _
        simp only [belief, trivialSignal]
        exact bayes_same μ 1
      | succ k ih =>
        intro hk
        have hkT : k < T := by omega
        rw [belief, histAt_succ_init, histAt_succ_last, ih (by omega)]
        simp only [Promo.at, Pricing.at, hkT, dif_pos]
        have hl : ∀ yy : Bool, likelihood M true (a ps true) ps yy =
            likelihood M false (a ps false) ps yy := by
          intro yy; simp only [likelihood, hsale]
        rw [hl]
        exact bayes_same _ _
    have h1 := key (t + 1) (by omega)
    have h0 := key 0 (by omega)
    rw [show ((t : ℕ) + 1 : ℕ) = (t : ℕ) + 1 from rfl] at h1
    rw [h1, h0]
