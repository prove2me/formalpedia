-- Prove2me | solution 1 for ConfoundPromo.LongRun.optimal_confounding_policy
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:41:13.210997+00:00
-- url     : https://prove2.me/submissions/ed7ad17c-60b0-4dc2-9896-dc1a52347f4a

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

open ConfoundPromo.LongRun
open Finset

namespace CPSolOCP

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

end CPSolOCP

namespace CPSolOCP

/-- Existence of a myopic choice at any belief for a valid single-price rule. -/
lemma exists_myopic (M : Market) (hM : M.Standing) (a : ℝ → Bool → ℝ) (ha : IsValidRule a)
    (pbar : ℝ) (hpbar : pbar ∈ M.price) (hsing : ∀ q ∈ M.price, q ≠ pbar → ∀ b, a q b = 0)
    (μ' : ℝ) (hμ' : μ' ∈ Set.Icc (0:ℝ) 1) : ∃ p, IsMyopicChoice M μ' a p := by
  set P := M.price with hP
  have hφL := hM.phiL_pos
  have hφLH := hM.phiL_lt_phiH
  have hφH := hM.phiH_lt_one
  obtain ⟨hμ0, hμ1⟩ := hμ'
  set c : ℝ := μ' * (1 - M.phiH) + (1 - μ') * (1 - M.phiL) with hc
  have hcpos : 0 < c := by nlinarith
  set U : ℝ → ℝ := fun q => c * (q * M.rhoC q) with hU
  set V : ℝ → ℝ := fun q => expRev M μ' a q with hV
  have hVU : ∀ q ∈ P, q ≠ pbar → V q = U q := by
    intro q hq hne
    simp only [hV, hU, expRev, saleProb, Market.phiVal, hsing q hq hne, if_true,
      Bool.false_eq_true, if_false, hc]
    ring
  have hPne : P.Nonempty := ⟨0, hM.pLo_nonpos, hM.pHi_nonneg⟩
  have hcontc : ContinuousOn M.rhoC P := by
    obtain ⟨K, hK⟩ := hM.rhoC_lipschitz; exact hK.continuousOn
  have hUc : ContinuousOn U P := continuousOn_const.mul (continuousOn_id.mul hcontc)
  obtain ⟨qu, hqu, hmax⟩ := (isCompact_Icc : IsCompact P).exists_isMaxOn hPne hUc
  have h0P : (0:ℝ) ∈ P := ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩
  have hstrict : ∀ q ∈ P, q ≠ qu → U q < U qu := by
    intro q hq hne
    have hs := hM.revC_strictConcave.2 hq hqu hne (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    have hm : (1/2 : ℝ) • q + (1/2 : ℝ) • qu ∈ P :=
      (convex_Icc M.pLo M.pHi) hq hqu (by norm_num) (by norm_num) (by norm_num)
    have hUm : U ((1/2 : ℝ) • q + (1/2 : ℝ) • qu) ≤ U qu := hmax hm
    simp only [smul_eq_mul] at hs hUm
    simp only [hU] at hUm ⊢
    have := mul_lt_mul_of_pos_left hs hcpos
    linear_combination 2 * this + 2 * hUm
  have hneg : ∀ q ∈ P, q < 0 → 0 < M.rhoC q := by
    intro q hq hq0
    by_contra hcon
    have hz : M.rhoC q = 0 := le_antisymm (not_lt.mp hcon) (hM.rhoC_nonneg q hq)
    have hs := hM.revC_strictConcave.2 hq h0P (ne_of_lt hq0) (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    have hm : (1/2 : ℝ) • q + (1/2 : ℝ) • (0:ℝ) ∈ P :=
      (convex_Icc M.pLo M.pHi) hq h0P (by norm_num) (by norm_num) (by norm_num)
    have hnn := hM.rhoC_nonneg _ hm
    simp only [smul_eq_mul, hz, mul_zero, zero_mul, add_zero] at hs hnn
    nlinarith
  -- every value is bounded by max (V pbar) (V qu)
  have hbound : ∀ q ∈ P, q ≠ pbar → q ≠ qu → V q < max (V pbar) (V qu) := by
    intro q hq hne1 hne2
    rw [hVU q hq hne1]
    have h1 := hstrict q hq hne2
    by_cases hqp : qu = pbar
    · -- then pbar ≥ 0 and V pbar ≥ U pbar
      have hpb0 : 0 ≤ pbar := by
        by_contra hlt
        push_neg at hlt
        have hU0 : U 0 ≤ U qu := hmax h0P
        have := hneg pbar hpbar hlt
        simp only [hU, zero_mul, mul_zero] at hU0
        rw [hqp] at hU0
        nlinarith [mul_pos hcpos this, mul_neg_of_neg_of_pos hlt (mul_pos hcpos this)]
      have hVge : U pbar ≤ V pbar := by
        simp only [hV, hU, expRev, saleProb, Market.phiVal, if_true, Bool.false_eq_true,
          if_false, hc]
        have hr0 : 0 ≤ M.rho0 pbar := le_trans (hM.rhoC_nonneg _ hpbar) (hM.rhoC_le_rho0 _ hpbar)
        have hat := (ha pbar true).1
        have haf := (ha pbar false).1
        have : 0 ≤ pbar * (μ' * (M.phiH * a pbar true * M.rho0 pbar) +
            (1 - μ') * (M.phiL * a pbar false * M.rho0 pbar)) := by
          apply mul_nonneg hpb0
          apply add_nonneg
          · exact mul_nonneg hμ0 (mul_nonneg (mul_nonneg (by linarith) hat) hr0)
          · exact mul_nonneg (by linarith) (mul_nonneg (mul_nonneg hφL.le haf) hr0)
        nlinarith
      rw [hqp] at h1
      exact lt_of_lt_of_le (lt_of_lt_of_le h1 hVge) (le_max_left _ _)
    · rw [← hVU qu hqu hqp] at h1
      exact lt_of_lt_of_le h1 (le_max_right _ _)
  set S : ℝ → ℝ := fun q => expSurplus M μ' a q with hS
  by_cases hcase : V qu < V pbar ∨ (V qu = V pbar ∧ S qu ≤ S pbar)
  · refine ⟨pbar, hpbar, ?_, ?_⟩
    · intro q hq
      have hm : max (V pbar) (V qu) = V pbar := by
        rcases hcase with h | h
        · exact max_eq_left h.le
        · exact max_eq_left h.1.le
      by_cases h1 : q = pbar
      · rw [h1]
      by_cases h2 : q = qu
      · rw [h2]; have := le_max_right (V pbar) (V qu); rw [hm] at this; exact this
      · have := hbound q hq h1 h2; rw [hm] at this; exact this.le
    · intro q hq heq
      by_cases h1 : q = pbar
      · rw [h1]
      by_cases h2 : q = qu
      · rw [h2]
        rcases hcase with h | h
        · exfalso; rw [h2] at heq; exact absurd heq (ne_of_lt h)
        · exact h.2
      · exfalso
        have := hbound q hq h1 h2
        have hm : max (V pbar) (V qu) = V pbar := by
          rcases hcase with h | h
          · exact max_eq_left h.le
          · exact max_eq_left h.1.le
        rw [hm] at this
        exact absurd heq (ne_of_lt this)
  · push_neg at hcase
    obtain ⟨hge, himp⟩ := hcase
    refine ⟨qu, hqu, ?_, ?_⟩
    · intro q hq
      have hm : max (V pbar) (V qu) = V qu := max_eq_right hge
      by_cases h1 : q = pbar
      · rw [h1]; exact hge
      by_cases h2 : q = qu
      · rw [h2]
      · have := hbound q hq h1 h2; rw [hm] at this; exact this.le
    · intro q hq heq
      by_cases h2 : q = qu
      · rw [h2]
      by_cases h1 : q = pbar
      · rw [h1] at heq ⊢
        have := himp heq.symm
        exact this.le
      · exfalso
        have := hbound q hq h1 h2
        have hm : max (V pbar) (V qu) = V qu := max_eq_right hge
        rw [hm] at this
        exact absurd heq (ne_of_lt this)

end CPSolOCP

open CPSolOCP

theorem solution (M : Market) (hM : M.Standing) (T : ℕ) (hT : 0 < T)
    (μ1 : ℝ) (hμ1 : μ1 ∈ Set.Icc (0 : ℝ) 1) (a : ℝ → Bool → ℝ) (p : ℝ)
    (ha : IsValidRule a) (hsingle : ∃ pbar ∈ M.price, ∀ q ∈ M.price, q ≠ pbar → ∀ b, a q b = 0)
    (hmy : IsMyopicChoice M μ1 a p) (hconf : IsConfoundingChoice M μ1 a p) :
    ∃ (α : Promo 1 T) (π : Pricing 1 T), α.IsValid ∧ (∀ t q b h, α t q b h = a q b) ∧
      IsBeliefBased M μ1 trivialSignal α ∧ IsSinglePrice M α ∧
      IsMyopic M μ1 trivialSignal α π ∧ IsConfounding M μ1 trivialSignal α π ∧
      surplusT M μ1 trivialSignal α π = T * expSurplus M μ1 a p := by
  obtain ⟨pbar, hpbar, hsing⟩ := hsingle
  have hex : ∀ μ' : ℝ, μ' ∈ Set.Icc (0:ℝ) 1 → ∃ q, IsMyopicChoice M μ' a q :=
    fun μ' hμ' => exists_myopic M hM a ha pbar hpbar hsing μ' hμ'
  choose f hf using hex
  set α : Promo 1 T := fun _ q b _ => a q b with hαdef
  set π : Pricing 1 T := fun t h =>
    if hb : belief M μ1 trivialSignal α t h = μ1 then p
    else if hb' : belief M μ1 trivialSignal α t h ∈ Set.Icc (0:ℝ) 1 then
      f _ hb' else 0 with hπdef
  have hsigv : (trivialSignal).IsValid := by
    refine ⟨fun _ _ => zero_le_one, fun _ => ?_⟩
    simp [trivialSignal]
  have hαv : α.IsValid := fun _ q b _ => ha q b
  -- beliefs along paths
  have key : ∀ (s : Fin 1) (y : Fin T → Bool) (k : ℕ), k ≤ T →
      belief M μ1 trivialSignal α k (histAt π s y k) = μ1 := by
    intro s y k
    induction k with
    | zero =>
      intro _
      simp only [belief, trivialSignal]
      exact bayes_same μ1 1
    | succ k ih =>
      intro hk
      have hkT : k < T := by omega
      have hbk := ih (by omega)
      rw [belief, histAt_succ_init, histAt_succ_last, hbk]
      have hpk : π.at k (histAt π s y k) = p := by
        simp only [Pricing.at, hkT, dif_pos, hπdef]
        rw [dif_pos hbk]
      rw [hpk]
      simp only [Promo.at, hkT, dif_pos, hαdef]
      exact hconf _
  have hprice : ∀ (s : Fin 1) (y : Fin T → Bool) (t : Fin T), priceAt π s y t = p := by
    intro s y t
    have hb := key s y t (by omega)
    simp only [priceAt, Pricing.at, t.isLt, dif_pos, hπdef]
    rw [dif_pos hb]
  have hpromo : ∀ (b : Bool) (s : Fin 1) (y : Fin T → Bool) (t : Fin T),
      promoAt α π b s y t = a p b := by
    intro b s y t
    simp only [promoAt, Promo.at, t.isLt, dif_pos, hαdef]
    rw [show priceAt π s y t = p from hprice s y t]
  refine ⟨α, π, hαv, fun _ _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro t h h' _ _ _ q _ b; rfl
  · intro t h _
    exact ⟨pbar, hpbar, fun q hq hne b => hsing q hq hne b⟩
  · intro t h hh
    have hmem := belief_mem M hM μ1 hμ1 trivialSignal hsigv α hαv t h hh
    show IsMyopicChoice M (belief M μ1 trivialSignal α t h) (fun q b => a q b) (π t h)
    simp only [hπdef]
    by_cases hb : belief M μ1 trivialSignal α t h = μ1
    · rw [dif_pos hb, hb]; exact hmy
    · rw [dif_neg hb, dif_pos hmem]; exact hf _ hmem
  · intro b s y _ t
    rw [key s y (t+1) (by omega), key s y 0 (by omega)]
  · -- the surplus
    have hpath : ∀ (b : Bool) (s : Fin 1) (y : Fin T → Bool),
        pathProb M α π b s y = ∏ t : Fin T, likelihood M b (a p b) p (y t) := by
      intro b s y
      unfold pathProb
      apply Finset.prod_congr rfl
      intro t _
      rw [hpromo, hprice]
    have hsum1 : ∀ b : Bool, ∑ y : Fin T → Bool, ∏ t : Fin T, likelihood M b (a p b) p (y t) = 1 := by
      intro b
      rw [← Fintype.prod_sum (fun (_ : Fin T) (c : Bool) => likelihood M b (a p b) p c)]
      apply Finset.prod_eq_one
      intro t _
      simp [likelihood]
    have hps : ∀ (b : Bool) (s : Fin 1) (y : Fin T → Bool),
        pathSurplus M α π b s y = T * surplus M b (a p b) p := by
      intro b s y
      unfold pathSurplus
      simp only [hpromo, hprice, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    unfold surplusT ConfoundPromo.LongRun.expect condExpect
    simp only [hps, hpath]
    have : ∀ b : Bool, ∑ y : Fin T → Bool, (∏ t : Fin T, likelihood M b (a p b) p (y t)) *
        (T * surplus M b (a p b) p) = T * surplus M b (a p b) p := by
      intro b
      rw [← Finset.sum_mul, hsum1, one_mul]
    simp only [this]
    simp [trivialSignal, prior, expSurplus]
    ring
