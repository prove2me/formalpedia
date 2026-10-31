-- Prove2me | solution 1 for ConfoundPromo.LongRun.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:51:22.306829+00:00
-- url     : https://prove2.me/submissions/8223f8a7-f553-4916-8b45-6146ba95d132

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model
import Theorems.Thm_ConfoundPromo_LongRun_proposition_1
import Theorems.Thm_ConfoundPromo_LongRun_upper_bound_display
import Theorems.Thm_ConfoundPromo_LongRun_signal_confounding_attains

open ConfoundPromo.LongRun
open Finset

namespace CPSolT1

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

end CPSolT1

namespace CPSolT1

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

end CPSolT1

namespace CPSolT1

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

end CPSolT1

open CPSolT1

theorem solution (M : Market) (hM : M.Standing) (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0 : ℝ) 1) :
    (∀ ε : ℝ, 0 < ε → ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → 0 < T →
      ∀ (n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T),
        sig.IsValid → α.IsValid → IsMyopic M μ0 sig α π →
        surplusT M μ0 sig α π / T ≤ co (WC M) μ0 + ε) ∧
    (∀ T : ℕ, 0 < T → ∃ (n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T),
      sig.IsValid ∧ α.IsValid ∧ IsBeliefBased M μ0 sig α ∧ IsMyopic M μ0 sig α π ∧
      IsConfounding M μ0 sig α π ∧ surplusT M μ0 sig α π / T = co (WC M) μ0) := by
  constructor
  · -- Part (i): Proposition 1 + the upper-bound display
    intro ε hε
    obtain ⟨Tbar, hTbar⟩ := upper_bound_display M hM (ε / 2) (by linarith) μ0 hμ0
    refine ⟨Tbar + 1, ?_⟩
    intro T hT hTpos n sig α π hsig hα hπ
    obtain ⟨sig', α', π', hs', ha', hsp, hbb, hmy', hle⟩ :=
      proposition_1 M hM μ0 hμ0 T hTpos n sig α π hsig hα hπ
    have h1 := hTbar T (by omega) 2 sig' α' π' hs' ha' hsp hbb hmy'
    have hTr : (0:ℝ) < T := by exact_mod_cast hTpos
    have h2 : surplusT M μ0 sig α π / T ≤ surplusT M μ0 sig' α' π' / T :=
      div_le_div_of_nonneg_right hle hTr.le
    linarith
  · -- Part (ii): the static existence statement, repeated over the horizon
    intro T hT
    obtain ⟨sig, a, p, hsig, hs, hsum⟩ := signal_confounding_attains M hM μ0 hμ0
    set μ1 : Fin 2 → ℝ := fun s => bayes μ0 (sig true s) (sig false s) with hμ1
    have hgood_dec : ∀ μ : ℝ, Decidable (μ = μ1 0 ∨ μ = μ1 1) := fun _ => Classical.dec _
    set rule : ℝ → ℝ → Bool → ℝ := fun μ =>
      if μ = μ1 0 ∨ μ = μ1 1 then a μ else fun _ _ => 0 with hrule
    have hrule_good : ∀ s : Fin 2, rule (μ1 s) = a (μ1 s) := by
      intro s
      simp only [hrule]
      rw [if_pos]
      fin_cases s
      · left; rfl
      · right; rfl
    have hrule_valid : ∀ μ, IsValidRule (rule μ) := by
      intro μ
      simp only [hrule]
      split_ifs with hg
      · rcases hg with hg | hg
        · rw [hg]; exact (hs 0).1
        · rw [hg]; exact (hs 1).1
      · intro q b; exact ⟨le_refl _, zero_le_one⟩
    have hzero_myo : ∀ μ' : ℝ, μ' ∈ Set.Icc (0:ℝ) 1 →
        ∃ q, IsMyopicChoice M μ' (fun _ _ => (0:ℝ)) q := by
      intro μ' hμ'
      exact exists_myopic M hM (fun _ _ => 0) (fun _ _ => ⟨le_refl _, zero_le_one⟩) 0
        ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩ (fun _ _ _ _ => rfl) μ' hμ'
    choose f hf using hzero_myo
    set bR := beliefR M T μ0 sig rule with hbR
    set α : Promo 2 T := fun t q b h => rule (bR t h) q b with hαdef
    set π : Pricing 2 T := fun t h =>
      if bR t h = μ1 0 ∨ bR t h = μ1 1 then p (bR t h)
      else if hb : bR t h ∈ Set.Icc (0:ℝ) 1 then f _ hb else 0 with hπdef
    have hbel : ∀ (t : ℕ) (h : SHist 2 t), belief M μ0 sig α t h = bR t h :=
      belief_eq_beliefR M T μ0 sig rule
    have hπeq : ∀ (t : Fin T) (h : SHist 2 t), (bR t h = μ1 0 ∨ bR t h = μ1 1) →
        π t h = p (bR t h) := by
      intro t h hg
      simp only [hπdef]
      rw [if_pos hg]
    have hαv : α.IsValid := fun t q b h => hrule_valid _ q b
    -- beliefs along paths
    have key : ∀ (s : Fin 2) (y : Fin T → Bool) (k : ℕ), k ≤ T →
        bR k (histAt π s y k) = μ1 s := by
      intro s y k
      induction k with
      | zero => intro _; simp [hbR, beliefR, histAt, hμ1]
      | succ k ih =>
        intro hk
        have hkT : k < T := by omega
        have hbk := ih (by omega)
        have hbk2 := hbk
        rw [hbR] at hbk2 ⊢
        rw [beliefR, histAt_succ_init, histAt_succ_last, hbk2]
        have hgood : μ1 s = μ1 0 ∨ μ1 s = μ1 1 := by
          fin_cases s
          · left; rfl
          · right; rfl
        have hpk : π.at k (histAt π s y k) = p (μ1 s) := by
          simp only [Pricing.at, hkT, dif_pos]
          have e : bR ((⟨k, hkT⟩ : Fin T) : ℕ) (histAt π s y k) = μ1 s := hbk
          have hg' : bR ((⟨k, hkT⟩ : Fin T) : ℕ) (histAt π s y k) = μ1 0 ∨
              bR ((⟨k, hkT⟩ : Fin T) : ℕ) (histAt π s y k) = μ1 1 := by
            rw [e]; exact hgood
          rw [hπeq _ _ hg']
          exact congrArg p e
        rw [hpk]
        simp only [if_pos hkT, hrule_good s]
        exact (hs s).2.2 _
    have hprice : ∀ (s : Fin 2) (y : Fin T → Bool) (t : Fin T), priceAt π s y t = p (μ1 s) := by
      intro s y t
      have hb := key s y t (by omega)
      have hgood : μ1 s = μ1 0 ∨ μ1 s = μ1 1 := by
        fin_cases s
        · left; rfl
        · right; rfl
      simp only [priceAt, Pricing.at, t.isLt, dif_pos]
      rw [hπeq _ _ (by rw [hb]; exact hgood)]
      exact congrArg p hb
    have hpromo : ∀ (b : Bool) (s : Fin 2) (y : Fin T → Bool) (t : Fin T),
        promoAt α π b s y t = a (μ1 s) (p (μ1 s)) b := by
      intro b s y t
      simp only [promoAt, Promo.at, t.isLt, dif_pos, hαdef]
      rw [key s y t (by omega), hprice s y t, hrule_good s]
    refine ⟨2, sig, α, π, hsig, hαv, ?_, ?_, ?_, ?_⟩
    · intro t h h' _ _ heq q _ b
      rw [hbel, hbel] at heq
      simp only [hαdef]
      rw [heq]
    · intro t h hh
      have hmem := belief_mem M hM μ0 hμ0 sig hsig α hαv t h hh
      rw [hbel] at hmem ⊢
      show IsMyopicChoice M (bR t h) (fun q b => rule (bR t h) q b) (π t h)
      simp only [hπdef]
      by_cases hg : bR t h = μ1 0 ∨ bR t h = μ1 1
      · rw [if_pos hg]
        rcases hg with hg | hg
        · rw [hg, hrule_good 0]; exact (hs 0).2.1
        · rw [hg, hrule_good 1]; exact (hs 1).2.1
      · rw [if_neg hg, dif_pos hmem]
        have : (fun q b => rule (bR t h) q b) = fun _ _ => (0:ℝ) := by
          funext q b; simp only [hrule, if_neg hg]
        rw [this]; exact hf _ hmem
    · intro b s y _ t
      rw [hbel, hbel, key s y (t+1) (by omega), key s y 0 (by omega)]
    · -- the surplus
      have hpath : ∀ (b : Bool) (s : Fin 2) (y : Fin T → Bool),
          pathProb M α π b s y = ∏ t : Fin T, likelihood M b (a (μ1 s) (p (μ1 s)) b) (p (μ1 s)) (y t) := by
        intro b s y
        unfold pathProb
        apply Finset.prod_congr rfl
        intro t _
        rw [hpromo, hprice]
      have hsum1 : ∀ (b : Bool) (s : Fin 2), ∑ y : Fin T → Bool,
          ∏ t : Fin T, likelihood M b (a (μ1 s) (p (μ1 s)) b) (p (μ1 s)) (y t) = 1 := by
        intro b s
        rw [← Fintype.prod_sum (fun (_ : Fin T) (c : Bool) =>
          likelihood M b (a (μ1 s) (p (μ1 s)) b) (p (μ1 s)) c)]
        apply Finset.prod_eq_one
        intro t _
        simp [likelihood]
      have hps : ∀ (b : Bool) (s : Fin 2) (y : Fin T → Bool),
          pathSurplus M α π b s y = T * surplus M b (a (μ1 s) (p (μ1 s)) b) (p (μ1 s)) := by
        intro b s y
        unfold pathSurplus
        simp only [hpromo, hprice, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      have hinner : ∀ (b : Bool) (s : Fin 2), ∑ y : Fin T → Bool, pathProb M α π b s y *
          pathSurplus M α π b s y = T * surplus M b (a (μ1 s) (p (μ1 s)) b) (p (μ1 s)) := by
        intro b s
        simp only [hpath, hps]
        rw [← Finset.sum_mul, hsum1, one_mul]
      have hST : surplusT M μ0 sig α π =
          T * ∑ s : Fin 2, (μ0 * sig true s * surplus M true (a (μ1 s) (p (μ1 s)) true) (p (μ1 s)) +
            (1 - μ0) * sig false s * surplus M false (a (μ1 s) (p (μ1 s)) false) (p (μ1 s))) := by
        unfold surplusT ConfoundPromo.LongRun.expect condExpect
        simp only [hinner]
        simp only [Fintype.sum_bool, prior, if_true, Bool.false_eq_true, if_false,
          Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s _
        ring
      have hstat : ∀ s : Fin 2, (μ0 * sig true s + (1 - μ0) * sig false s) *
          expSurplus M (μ1 s) (a (μ1 s)) (p (μ1 s)) =
          μ0 * sig true s * surplus M true (a (μ1 s) (p (μ1 s)) true) (p (μ1 s)) +
            (1 - μ0) * sig false s * surplus M false (a (μ1 s) (p (μ1 s)) false) (p (μ1 s)) := by
        intro s
        have hb := bayes_mul μ0 (sig true s) (sig false s) hμ0 (hsig.1 _ _) (hsig.1 _ _)
        simp only [hμ1] at hb ⊢
        unfold expSurplus
        linear_combination
          (surplus M true (a (bayes μ0 (sig true s) (sig false s))
              (p (bayes μ0 (sig true s) (sig false s))) true)
              (p (bayes μ0 (sig true s) (sig false s))) -
            surplus M false (a (bayes μ0 (sig true s) (sig false s))
              (p (bayes μ0 (sig true s) (sig false s))) false)
              (p (bayes μ0 (sig true s) (sig false s)))) * hb
      have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
      rw [hST, ← Finset.sum_congr rfl (fun s _ => hstat s)]
      simp only [hμ1]
      rw [hsum]
      field_simp
