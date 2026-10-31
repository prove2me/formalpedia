-- Prove2me | solution 1 for ConfoundPromo.LongRun.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T08:07:41.689918+00:00
-- url     : https://prove2.me/submissions/1b49c199-d820-4ecd-bbbe-8294075f5998

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

open ConfoundPromo.LongRun
open Finset
open Filter Topology

namespace CPSolL4

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

end CPSolL4

namespace CPSolL4

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


/-! ## Concavity of the concavification -/

lemma co_concave (f : ℝ → ℝ) (B : ℝ) (hB : ∀ μ ∈ Set.Icc (0:ℝ) 1, f μ ≤ B) :
    ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (co f) := by
  set H : Set (ℝ × ℝ) := {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1} with hH
  set C := convexHull ℝ H with hC
  have hCB : ∀ z ∈ C, z.2 ≤ B := by
    have hsub : H ⊆ (LinearMap.snd ℝ ℝ ℝ) ⁻¹' Set.Iic B := by
      intro z hz
      simp only [Set.mem_preimage, LinearMap.snd_apply, Set.mem_Iic]
      exact le_trans hz.2 (hB _ hz.1)
    intro z hz
    have := convexHull_min hsub ((convex_Iic B).linear_preimage (LinearMap.snd ℝ ℝ ℝ)) hz
    simpa using this
  have hbdd : ∀ μ : ℝ, BddAbove {z | (μ, z) ∈ C} := fun μ => ⟨B, fun z hz => hCB _ hz⟩
  have hne : ∀ μ ∈ Set.Icc (0:ℝ) 1, ({z | (μ, z) ∈ C}).Nonempty :=
    fun μ hμ => ⟨f μ, subset_convexHull ℝ H ⟨hμ, le_refl _⟩⟩
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  by_contra hlt
  push_neg at hlt
  set g := a * co f x + b * co f y - co f (a * x + b * y) with hg
  have hgpos : 0 < g := by linarith
  obtain ⟨z1, hz1, hz1'⟩ := exists_lt_of_lt_csSup (hne x hx) (by linarith : co f x - g/2 < co f x)
  obtain ⟨z2, hz2, hz2'⟩ := exists_lt_of_lt_csSup (hne y hy) (by linarith : co f y - g/2 < co f y)
  have hmem : (a * x + b * y, a * z1 + b * z2) ∈ C := by
    have := (convex_convexHull ℝ H) hz1 hz2 ha hb hab
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using this
  have hle : a * z1 + b * z2 ≤ co f (a * x + b * y) := le_csSup (hbdd _) hmem
  nlinarith [mul_le_mul_of_nonneg_left hz1'.le ha, mul_le_mul_of_nonneg_left hz2'.le hb]

/-! ## Boundedness of W^C -/

lemma surplus_le (M : Market) (hM : M.Standing) (b : Bool) (a p : ℝ)
    (ha : a ∈ Set.Icc (0:ℝ) 1) (hp : p ∈ M.price) :
    surplus M b a p ≤ |M.Wout| + |M.W0 M.pLo| + |M.Wc M.pLo| := by
  have hφ0 : 0 ≤ M.phiVal b := by
    unfold Market.phiVal; split_ifs <;> linarith [hM.phiL_pos, hM.phiL_lt_phiH]
  have hφ1 : M.phiVal b ≤ 1 := by
    unfold Market.phiVal; split_ifs <;> linarith [hM.phiL_lt_phiH, hM.phiH_lt_one]
  have hLo : M.pLo ∈ M.price := ⟨le_refl _, le_trans hM.pLo_nonpos hM.pHi_nonneg⟩
  have hW0 : M.W0 p ≤ M.W0 M.pLo := hM.W0_antitone hLo hp hp.1
  have hWc : M.Wc p ≤ M.Wc M.pLo := hM.Wc_antitone hLo hp hp.1
  obtain ⟨ha0, ha1⟩ := ha
  have h1 : M.Wout + a * (M.W0 p - M.Wout) ≤ |M.Wout| + |M.W0 M.pLo| := by
    have e1 : (1 - a) * M.Wout ≤ (1 - a) * |M.Wout| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
    have e2 : a * M.W0 p ≤ a * |M.W0 M.pLo| :=
      mul_le_mul_of_nonneg_left (le_trans hW0 (le_abs_self _)) ha0
    have e3 : (1 - a) * |M.Wout| ≤ |M.Wout| := by nlinarith [abs_nonneg M.Wout]
    have e4 : a * |M.W0 M.pLo| ≤ |M.W0 M.pLo| := by nlinarith [abs_nonneg (M.W0 M.pLo)]
    nlinarith
  have h2 : M.phiVal b * (M.Wout + a * (M.W0 p - M.Wout)) ≤ |M.Wout| + |M.W0 M.pLo| := by
    have := mul_le_mul_of_nonneg_left h1 hφ0
    have hpos : 0 ≤ |M.Wout| + |M.W0 M.pLo| := by positivity
    nlinarith
  have h3 : (1 - M.phiVal b) * M.Wc p ≤ |M.Wc M.pLo| := by
    have := mul_le_mul_of_nonneg_left (le_trans hWc (le_abs_self _)) (by linarith : 0 ≤ 1 - M.phiVal b)
    nlinarith [abs_nonneg (M.Wc M.pLo)]
  unfold surplus
  linarith

lemma WC_le (M : Market) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1) :
    WC M μ ≤ max 0 (|M.Wout| + |M.W0 M.pLo| + |M.Wc M.pLo|) := by
  unfold WC
  set S := {v | ∃ (a : ℝ → Bool → ℝ) (p : ℝ), IsValidRule a ∧ IsMyopicChoice M μ a p ∧
    IsConfoundingChoice M μ a p ∧ v = expSurplus M μ a p} with hS
  rcases Set.eq_empty_or_nonempty S with h | h
  · rw [h, Real.sSup_empty]; exact le_max_left _ _
  · apply le_trans _ (le_max_right _ _)
    apply csSup_le h
    rintro v ⟨a, p, ha, hmy, _, rfl⟩
    have h1 := surplus_le M hM true (a p true) p (ha p true) hmy.1
    have h2 := surplus_le M hM false (a p false) p (ha p false) hmy.1
    unfold expSurplus
    obtain ⟨h0, h1'⟩ := hμ
    nlinarith


lemma le_co (f : ℝ → ℝ) (B : ℝ) (hB : ∀ μ ∈ Set.Icc (0:ℝ) 1, f μ ≤ B) (μ : ℝ)
    (hμ : μ ∈ Set.Icc (0:ℝ) 1) : f μ ≤ co f μ := by
  set H : Set (ℝ × ℝ) := {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1} with hH
  set C := convexHull ℝ H with hC
  have hCB : ∀ z ∈ C, z.2 ≤ B := by
    have hsub : H ⊆ (LinearMap.snd ℝ ℝ ℝ) ⁻¹' Set.Iic B := by
      intro z hz
      simp only [Set.mem_preimage, LinearMap.snd_apply, Set.mem_Iic]
      exact le_trans hz.2 (hB _ hz.1)
    intro z hz
    have := convexHull_min hsub ((convex_Iic B).linear_preimage (LinearMap.snd ℝ ℝ ℝ)) hz
    simpa using this
  unfold co
  apply le_csSup ⟨B, fun z hz => hCB _ hz⟩
  exact subset_convexHull ℝ H ⟨hμ, le_refl _⟩

lemma Wmax_bdd (M : Market) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1) :
    BddAbove {v | ∃ (a : ℝ → Bool → ℝ) (p : ℝ), IsValidRule a ∧ IsMyopicChoice M μ a p ∧
      v = expSurplus M μ a p} := by
  refine ⟨|M.Wout| + |M.W0 M.pLo| + |M.Wc M.pLo|, ?_⟩
  rintro v ⟨a, p, ha, hmy, rfl⟩
  have h1 := surplus_le M hM true (a p true) p (ha p true) hmy.1
  have h2 := surplus_le M hM false (a p false) p (ha p false) hmy.1
  unfold expSurplus
  obtain ⟨h0, h1'⟩ := hμ
  nlinarith

lemma Wmax_le (M : Market) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1) :
    Wmax M μ ≤ max 0 (|M.Wout| + |M.W0 M.pLo| + |M.Wc M.pLo|) := by
  unfold Wmax
  set S := {v | ∃ (a : ℝ → Bool → ℝ) (p : ℝ), IsValidRule a ∧ IsMyopicChoice M μ a p ∧
    v = expSurplus M μ a p} with hS
  rcases Set.eq_empty_or_nonempty S with h | h
  · rw [h, Real.sSup_empty]; exact le_max_left _ _
  · apply le_trans _ (le_max_right _ _)
    apply csSup_le h
    rintro v ⟨a, p, ha, hmy, rfl⟩
    have h1 := surplus_le M hM true (a p true) p (ha p true) hmy.1
    have h2 := surplus_le M hM false (a p false) p (ha p false) hmy.1
    unfold expSurplus
    obtain ⟨h0, h1'⟩ := hμ
    nlinarith


end CPSolL4

namespace CPSolL4

lemma Wmax_nonempty (M : Market) (hM : M.Standing) (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1) :
    {v | ∃ (a : ℝ → Bool → ℝ) (p : ℝ), IsValidRule a ∧ IsMyopicChoice M μ a p ∧
      v = expSurplus M μ a p}.Nonempty := by
  obtain ⟨p, hp⟩ := exists_myopic M hM (fun _ _ => 0) (fun _ _ => ⟨le_refl _, zero_le_one⟩) 0
    ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩ (fun _ _ _ _ => rfl) μ hμ
  exact ⟨_, _, _, fun _ _ => ⟨le_refl _, zero_le_one⟩, hp, rfl⟩

lemma conf_zero (M : Market) (a : ℝ → Bool → ℝ) (p : ℝ) : IsConfoundingChoice M 0 a p := by
  intro y; unfold bayes; split_ifs <;> simp

lemma conf_one (M : Market) (a : ℝ → Bool → ℝ) (p : ℝ) : IsConfoundingChoice M 1 a p := by
  intro y; unfold bayes; split_ifs with h
  · rfl
  · simp only [one_mul, sub_self, zero_mul, add_zero] at h ⊢
    exact div_self h

lemma WC_eq_Wmax_zero (M : Market) : WC M 0 = Wmax M 0 := by
  unfold WC Wmax
  congr 1
  ext v
  constructor
  · rintro ⟨a, p, ha, hm, _, rfl⟩; exact ⟨a, p, ha, hm, rfl⟩
  · rintro ⟨a, p, ha, hm, rfl⟩; exact ⟨a, p, ha, hm, conf_zero M a p, rfl⟩

lemma WC_eq_Wmax_one (M : Market) : WC M 1 = Wmax M 1 := by
  unfold WC Wmax
  congr 1
  ext v
  constructor
  · rintro ⟨a, p, ha, hm, _, rfl⟩; exact ⟨a, p, ha, hm, rfl⟩
  · rintro ⟨a, p, ha, hm, rfl⟩; exact ⟨a, p, ha, hm, conf_one M a p, rfl⟩

lemma co_le_affine (f : ℝ → ℝ) (c d : ℝ) (h : ∀ x ∈ Set.Icc (0:ℝ) 1, f x ≤ c + d * x)
    (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1) : co f μ ≤ c + d * μ := by
  set H : Set (ℝ × ℝ) := {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1} with hH
  set L : ℝ × ℝ →ₗ[ℝ] ℝ := LinearMap.snd ℝ ℝ ℝ - d • LinearMap.fst ℝ ℝ ℝ with hL
  have hsub : H ⊆ L ⁻¹' Set.Iic c := by
    intro z hz
    simp only [Set.mem_preimage, Set.mem_Iic, hL, LinearMap.sub_apply, LinearMap.snd_apply,
      LinearMap.smul_apply, LinearMap.fst_apply, smul_eq_mul]
    have := h _ hz.1
    linarith [hz.2]
  unfold co
  apply csSup_le
  · exact ⟨f μ, subset_convexHull ℝ H ⟨hμ, le_refl _⟩⟩
  · intro z hz
    have := convexHull_min hsub ((convex_Iic c).linear_preimage L) hz
    simp only [Set.mem_preimage, Set.mem_Iic, hL, LinearMap.sub_apply, LinearMap.snd_apply,
      LinearMap.smul_apply, LinearMap.fst_apply, smul_eq_mul] at this
    linarith

lemma chord_le_co (f : ℝ → ℝ) (B : ℝ) (hB : ∀ μ ∈ Set.Icc (0:ℝ) 1, f μ ≤ B) (μ : ℝ)
    (hμ : μ ∈ Set.Icc (0:ℝ) 1) : (1 - μ) * f 0 + μ * f 1 ≤ co f μ := by
  set H : Set (ℝ × ℝ) := {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1} with hH
  set C := convexHull ℝ H with hC
  have hCB : ∀ z ∈ C, z.2 ≤ B := by
    have hsub : H ⊆ (LinearMap.snd ℝ ℝ ℝ) ⁻¹' Set.Iic B := by
      intro z hz
      simp only [Set.mem_preimage, LinearMap.snd_apply, Set.mem_Iic]
      exact le_trans hz.2 (hB _ hz.1)
    intro z hz
    have := convexHull_min hsub ((convex_Iic B).linear_preimage (LinearMap.snd ℝ ℝ ℝ)) hz
    simpa using this
  unfold co
  apply le_csSup ⟨B, fun z hz => hCB _ hz⟩
  have h0 : ((0:ℝ), f 0) ∈ C := subset_convexHull ℝ H ⟨⟨le_refl _, zero_le_one⟩, le_refl _⟩
  have h1 : ((1:ℝ), f 1) ∈ C := subset_convexHull ℝ H ⟨⟨zero_le_one, le_refl _⟩, le_refl _⟩
  have := (convex_convexHull ℝ H) h0 h1 (by linarith [hμ.2] : (0:ℝ) ≤ 1 - μ) hμ.1 (by ring)
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_zero, mul_one, zero_add] at this
  exact this

lemma usc0 (M : Market) (hM : M.Standing) :
    ∀ η > 0, ∃ δ > 0, ∀ μ ∈ Set.Icc (0:ℝ) 1, μ ≤ δ → Wmax M μ ≤ Wmax M 0 + η := by
  intro η hη
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ k : ℕ, ∃ μ ∈ Set.Icc (0:ℝ) 1, μ ≤ 1 / ((k:ℝ) + 1) ∧ Wmax M 0 + η < Wmax M μ :=
    fun k => hcon _ (by positivity)
  choose μs hμs hμle hμgt using hseq
  have hpick : ∀ k, ∃ (a : ℝ → Bool → ℝ) (p : ℝ), IsValidRule a ∧ IsMyopicChoice M (μs k) a p ∧
      Wmax M 0 + η < expSurplus M (μs k) a p := by
    intro k
    obtain ⟨v, ⟨a, p, ha, hm, rfl⟩, hv⟩ :=
      exists_lt_of_lt_csSup (Wmax_nonempty M hM _ (hμs k)) (hμgt k)
    exact ⟨a, p, ha, hm, hv⟩
  choose as ps has hms hgt using hpick
  have hφL := hM.phiL_pos
  have hφLH := hM.phiL_lt_phiH
  have hφH := hM.phiH_lt_one
  set K : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ M.price with hK
  set x : ℕ → ℝ × ℝ := fun k => (as k (ps k) false, ps k) with hx
  have hxK : ∀ k, x k ∈ K := fun k => ⟨has k (ps k) false, (hms k).1⟩
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨xb, hxbK, φ, hφ, hlim⟩ := hKc.tendsto_subseq hxK
  have hμ0 : Tendsto μs atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
    · intro k; exact (hμs k).1
    · intro k; exact hμle k
  have hμφ : Tendsto (fun k => μs (φ k)) atTop (𝓝 0) := hμ0.comp hφ.tendsto_atTop
  have hW0c : ContinuousOn M.W0 M.price := by
    obtain ⟨L, hL⟩ := hM.W0_lipschitz; exact hL.continuousOn
  have hWcc : ContinuousOn M.Wc M.price := by
    obtain ⟨L, hL⟩ := hM.Wc_lipschitz; exact hL.continuousOn
  have hr0c : ContinuousOn M.rho0 M.price := by
    obtain ⟨L, hL⟩ := hM.rho0_lipschitz; exact hL.continuousOn
  have hrcc : ContinuousOn M.rhoC M.price := by
    obtain ⟨L, hL⟩ := hM.rhoC_lipschitz; exact hL.continuousOn
  have hsnd : Set.MapsTo (fun z : ℝ × ℝ => z.2) K M.price := fun z hz => hz.2
  set S : ℝ × ℝ → ℝ := fun z => surplus M false z.1 z.2 with hS
  set Rv : ℝ × ℝ → ℝ := fun z => z.2 * saleProb M false z.1 z.2 with hRv
  have hSc : ContinuousOn S K := by
    have h2 : ContinuousOn (fun z : ℝ × ℝ => M.W0 z.2) K := hW0c.comp continuousOn_snd hsnd
    have h3 : ContinuousOn (fun z : ℝ × ℝ => M.Wc z.2) K := hWcc.comp continuousOn_snd hsnd
    simp only [hS, surplus]
    exact (continuousOn_const.mul (continuousOn_const.add
      (continuousOn_fst.mul (h2.sub continuousOn_const)))).add (continuousOn_const.mul h3)
  have hRc : ContinuousOn Rv K := by
    have h2 : ContinuousOn (fun z : ℝ × ℝ => M.rho0 z.2) K := hr0c.comp continuousOn_snd hsnd
    have h3 : ContinuousOn (fun z : ℝ × ℝ => M.rhoC z.2) K := hrcc.comp continuousOn_snd hsnd
    simp only [hRv, saleProb]
    exact continuousOn_snd.mul (((continuousOn_const.mul continuousOn_fst).mul h2).add
      (continuousOn_const.mul h3))
  have hxφ : Tendsto (fun k => x (φ k)) atTop (𝓝[K] xb) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun k => hxK _)⟩
  have hSlim : Tendsto (fun k => S (x (φ k))) atTop (𝓝 (S xb)) :=
    (hSc xb hxbK).tendsto.comp hxφ
  have hRlim : Tendsto (fun k => Rv (x (φ k))) atTop (𝓝 (Rv xb)) :=
    (hRc xb hxbK).tendsto.comp hxφ
  -- (i) the limit surplus exceeds Wmax 0 + η
  set Bs := |M.Wout| + |M.W0 M.pLo| + |M.Wc M.pLo| with hBs
  have hi : Wmax M 0 + η ≤ S xb := by
    have hub : ∀ k, Wmax M 0 + η < μs (φ k) * Bs + (1 - μs (φ k)) * S (x (φ k)) := by
      intro k
      have h := hgt (φ k)
      have hH := surplus_le M hM true (as (φ k) (ps (φ k)) true) (ps (φ k)) (has _ _ _) (hms _).1
      unfold expSurplus at h
      have hm0 := (hμs (φ k)).1
      simp only [hS, hx]
      nlinarith
    have hT : Tendsto (fun k => μs (φ k) * Bs + (1 - μs (φ k)) * S (x (φ k))) atTop
        (𝓝 (0 * Bs + (1 - 0) * S xb)) :=
      (hμφ.mul tendsto_const_nhds).add ((tendsto_const_nhds.sub hμφ).mul hSlim)
    simp only [zero_mul, sub_zero, one_mul, zero_add] at hT
    exact ge_of_tendsto' hT (fun k => (hub k).le)
  -- (ii) the limit revenue dominates every unpromoted revenue at nonnegative prices
  set Pm := |M.pLo| + |M.pHi| with hPm
  have hii : ∀ q ∈ M.price, 0 ≤ q → q * ((1 - M.phiL) * M.rhoC q) ≤ Rv xb := by
    intro q hq hq0
    have hk : ∀ k, (1 - μs (φ k)) * (q * ((1 - M.phiL) * M.rhoC q)) ≤
        μs (φ k) * Pm + (1 - μs (φ k)) * Rv (x (φ k)) := by
      intro k
      set μk := μs (φ k)
      set a := as (φ k)
      set p := ps (φ k)
      have hmy := (hms (φ k)).2.1 q hq
      have hm := (hμs (φ k))
      have hp := (hms (φ k)).1
      unfold expRev at hmy
      have hsHq := saleProb_mem M hM true (a q true) q (has _ _ _) hq
      have hsLq := saleProb_mem M hM false (a q false) q (has _ _ _) hq
      have hsHp := saleProb_mem M hM true (a p true) p (has _ _ _) hp
      have hsLp := saleProb_mem M hM false (a p false) p (has _ _ _) hp
      have hLq : (1 - M.phiL) * M.rhoC q ≤ saleProb M false (a q false) q := by
        unfold saleProb Market.phiVal
        simp only [Bool.false_eq_true, if_false]
        have := (has (φ k) q false).1
        have := le_trans (hM.rhoC_nonneg q hq) (hM.rhoC_le_rho0 q hq)
        nlinarith [mul_nonneg (mul_nonneg hφL.le (has (φ k) q false).1) this]
      have hpabs : p * saleProb M true (a p true) p ≤ Pm := by
        have h1 : p * saleProb M true (a p true) p ≤ |p| * saleProb M true (a p true) p :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hsHp.1
        have h2 : |p| * saleProb M true (a p true) p ≤ |p| :=
          mul_le_of_le_one_right (abs_nonneg _) hsHp.2
        have h3 : |p| ≤ Pm := by
          rw [hPm, abs_le]
          constructor
          · have := neg_abs_le M.pLo; have := hp.1; have := abs_nonneg M.pHi; linarith
          · have := le_abs_self M.pHi; have := hp.2; have := abs_nonneg M.pLo; linarith
        linarith
      simp only [hRv, hx]
      have e1 : q * (μk * saleProb M true (a q true) q + (1 - μk) * saleProb M false (a q false) q)
          ≥ (1 - μk) * (q * ((1 - M.phiL) * M.rhoC q)) := by
        have := mul_le_mul_of_nonneg_left hLq (by linarith [hm.2] : (0:ℝ) ≤ 1 - μk)
        have := mul_nonneg hm.1 hsHq.1
        nlinarith [mul_le_mul_of_nonneg_left this hq0]
      have e2 : p * (μk * saleProb M true (a p true) p + (1 - μk) * saleProb M false (a p false) p)
          ≤ μk * Pm + (1 - μk) * (p * saleProb M false (a p false) p) := by
        have := mul_le_mul_of_nonneg_left hpabs hm.1
        nlinarith
      linarith
    have hL : Tendsto (fun k => (1 - μs (φ k)) * (q * ((1 - M.phiL) * M.rhoC q))) atTop
        (𝓝 ((1 - 0) * (q * ((1 - M.phiL) * M.rhoC q)))) :=
      (tendsto_const_nhds.sub hμφ).mul tendsto_const_nhds
    have hR : Tendsto (fun k => μs (φ k) * Pm + (1 - μs (φ k)) * Rv (x (φ k))) atTop
        (𝓝 (0 * Pm + (1 - 0) * Rv xb)) :=
      (hμφ.mul tendsto_const_nhds).add ((tendsto_const_nhds.sub hμφ).mul hRlim)
    have := le_of_tendsto_of_tendsto' hL hR hk
    simpa using this
  -- (iii) a single-price rule at belief 0 realizes the limit
  obtain ⟨ab, pb⟩ := xb
  obtain ⟨hab, hpb⟩ := hxbK
  set b : ℝ → Bool → ℝ := fun q b' => if q = pb then (if b' then 0 else ab) else 0 with hbdef
  have hbv : IsValidRule b := by
    intro q b'
    simp only [hbdef]
    split_ifs
    · exact ⟨le_refl _, zero_le_one⟩
    · exact hab
    · exact ⟨le_refl _, zero_le_one⟩
  have hbs : ∀ q ∈ M.price, q ≠ pb → ∀ b', b q b' = 0 := by
    intro q _ hq b'; simp [hbdef, hq]
  obtain ⟨p', hp'⟩ := exists_myopic M hM b hbv pb hpb hbs 0 ⟨le_refl _, zero_le_one⟩
  have hrev : ∀ q, expRev M 0 b q = q * saleProb M false (b q false) q := by
    intro q; simp [expRev]
  have hsur : ∀ q, expSurplus M 0 b q = surplus M false (b q false) q := by
    intro q; simp [expSurplus]
  have hbpb : b pb false = ab := by simp [hbdef]
  have hR0 : 0 ≤ Rv (ab, pb) := by
    have := hii 0 ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩ (le_refl _)
    simpa using this
  have hpb_max : expRev M 0 b p' ≤ expRev M 0 b pb := by
    rw [hrev, hrev, hbpb]
    by_cases hq : p' = pb
    · rw [hq, hbpb]
    · have hb0 : b p' false = 0 := by simp [hbdef, hq]
      rw [hb0]
      have hval : p' * saleProb M false 0 p' = p' * ((1 - M.phiL) * M.rhoC p') := by
        simp [saleProb, Market.phiVal]
      rw [hval]
      have hRv : Rv (ab, pb) = pb * saleProb M false ab pb := rfl
      rcases le_or_gt 0 p' with h0 | h0
      · have := hii p' hp'.1 h0
        rw [hRv] at this; exact this
      · have hc := hM.rhoC_nonneg p' hp'.1
        have : p' * ((1 - M.phiL) * M.rhoC p') ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h0.le (mul_nonneg (by linarith) hc)
        rw [hRv] at hR0
        linarith
  have heq : expRev M 0 b pb = expRev M 0 b p' := le_antisymm (hp'.2.1 pb hpb) hpb_max
  have hS' := hp'.2.2 pb hpb heq
  have hW : expSurplus M 0 b p' ≤ Wmax M 0 :=
    le_csSup (Wmax_bdd M hM 0 ⟨le_refl _, zero_le_one⟩) ⟨b, p', hbv, hp', rfl⟩
  rw [hsur, hbpb] at hS'
  have hSxb : S (ab, pb) = surplus M false ab pb := rfl
  rw [hSxb] at hi
  linarith

lemma usc1 (M : Market) (hM : M.Standing) :
    ∀ η > 0, ∃ δ > 0, ∀ μ ∈ Set.Icc (0:ℝ) 1, 1 - δ ≤ μ → Wmax M μ ≤ Wmax M 1 + η := by
  intro η hη
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ k : ℕ, ∃ μ ∈ Set.Icc (0:ℝ) 1, 1 - 1 / ((k:ℝ) + 1) ≤ μ ∧ Wmax M 1 + η < Wmax M μ :=
    fun k => hcon _ (by positivity)
  choose μs hμs hμle hμgt using hseq
  have hpick : ∀ k, ∃ (a : ℝ → Bool → ℝ) (p : ℝ), IsValidRule a ∧ IsMyopicChoice M (μs k) a p ∧
      Wmax M 1 + η < expSurplus M (μs k) a p := by
    intro k
    obtain ⟨v, ⟨a, p, ha, hm, rfl⟩, hv⟩ :=
      exists_lt_of_lt_csSup (Wmax_nonempty M hM _ (hμs k)) (hμgt k)
    exact ⟨a, p, ha, hm, hv⟩
  choose as ps has hms hgt using hpick
  have hφL := hM.phiL_pos
  have hφLH := hM.phiL_lt_phiH
  have hφH := hM.phiH_lt_one
  set K : Set (ℝ × ℝ) := Set.Icc (0:ℝ) 1 ×ˢ M.price with hK
  set x : ℕ → ℝ × ℝ := fun k => (as k (ps k) true, ps k) with hx
  have hxK : ∀ k, x k ∈ K := fun k => ⟨has k (ps k) true, (hms k).1⟩
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨xb, hxbK, φ, hφ, hlim⟩ := hKc.tendsto_subseq hxK
  have hμ0 : Tendsto (fun k => 1 - μs k) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
    · intro k; linarith [(hμs k).2]
    · intro k; linarith [hμle k]
  have hμφ : Tendsto (fun k => 1 - μs (φ k)) atTop (𝓝 0) := hμ0.comp hφ.tendsto_atTop
  have hW0c : ContinuousOn M.W0 M.price := by
    obtain ⟨L, hL⟩ := hM.W0_lipschitz; exact hL.continuousOn
  have hWcc : ContinuousOn M.Wc M.price := by
    obtain ⟨L, hL⟩ := hM.Wc_lipschitz; exact hL.continuousOn
  have hr0c : ContinuousOn M.rho0 M.price := by
    obtain ⟨L, hL⟩ := hM.rho0_lipschitz; exact hL.continuousOn
  have hrcc : ContinuousOn M.rhoC M.price := by
    obtain ⟨L, hL⟩ := hM.rhoC_lipschitz; exact hL.continuousOn
  have hsnd : Set.MapsTo (fun z : ℝ × ℝ => z.2) K M.price := fun z hz => hz.2
  set S : ℝ × ℝ → ℝ := fun z => surplus M true z.1 z.2 with hS
  set Rv : ℝ × ℝ → ℝ := fun z => z.2 * saleProb M true z.1 z.2 with hRv
  have hSc : ContinuousOn S K := by
    have h2 : ContinuousOn (fun z : ℝ × ℝ => M.W0 z.2) K := hW0c.comp continuousOn_snd hsnd
    have h3 : ContinuousOn (fun z : ℝ × ℝ => M.Wc z.2) K := hWcc.comp continuousOn_snd hsnd
    simp only [hS, surplus]
    exact (continuousOn_const.mul (continuousOn_const.add
      (continuousOn_fst.mul (h2.sub continuousOn_const)))).add (continuousOn_const.mul h3)
  have hRc : ContinuousOn Rv K := by
    have h2 : ContinuousOn (fun z : ℝ × ℝ => M.rho0 z.2) K := hr0c.comp continuousOn_snd hsnd
    have h3 : ContinuousOn (fun z : ℝ × ℝ => M.rhoC z.2) K := hrcc.comp continuousOn_snd hsnd
    simp only [hRv, saleProb]
    exact continuousOn_snd.mul (((continuousOn_const.mul continuousOn_fst).mul h2).add
      (continuousOn_const.mul h3))
  have hxφ : Tendsto (fun k => x (φ k)) atTop (𝓝[K] xb) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun k => hxK _)⟩
  have hSlim : Tendsto (fun k => S (x (φ k))) atTop (𝓝 (S xb)) :=
    (hSc xb hxbK).tendsto.comp hxφ
  have hRlim : Tendsto (fun k => Rv (x (φ k))) atTop (𝓝 (Rv xb)) :=
    (hRc xb hxbK).tendsto.comp hxφ
  -- (i) the limit surplus exceeds Wmax 0 + η
  set Bs := |M.Wout| + |M.W0 M.pLo| + |M.Wc M.pLo| with hBs
  have hi : Wmax M 1 + η ≤ S xb := by
    have hub : ∀ k, Wmax M 1 + η < (1 - μs (φ k)) * Bs + (1 - (1 - μs (φ k))) * S (x (φ k)) := by
      intro k
      have h := hgt (φ k)
      have hH := surplus_le M hM false (as (φ k) (ps (φ k)) false) (ps (φ k)) (has _ _ _) (hms _).1
      unfold expSurplus at h
      have hm0 := (hμs (φ k)).2
      simp only [hS, hx]
      nlinarith
    have hT : Tendsto (fun k => (1 - μs (φ k)) * Bs + (1 - (1 - μs (φ k))) * S (x (φ k))) atTop
        (𝓝 (0 * Bs + (1 - 0) * S xb)) :=
      (hμφ.mul tendsto_const_nhds).add ((tendsto_const_nhds.sub hμφ).mul hSlim)
    simp only [zero_mul, sub_zero, one_mul, zero_add] at hT
    exact ge_of_tendsto' hT (fun k => (hub k).le)
  -- (ii) the limit revenue dominates every unpromoted revenue at nonnegative prices
  set Pm := |M.pLo| + |M.pHi| with hPm
  have hii : ∀ q ∈ M.price, 0 ≤ q → q * ((1 - M.phiH) * M.rhoC q) ≤ Rv xb := by
    intro q hq hq0
    have hk : ∀ k, (1 - (1 - μs (φ k))) * (q * ((1 - M.phiH) * M.rhoC q)) ≤
        (1 - μs (φ k)) * Pm + (1 - (1 - μs (φ k))) * Rv (x (φ k)) := by
      intro k
      set μk := μs (φ k)
      set a := as (φ k)
      set p := ps (φ k)
      have hmy := (hms (φ k)).2.1 q hq
      have hm := (hμs (φ k))
      have hp := (hms (φ k)).1
      unfold expRev at hmy
      have hsHq := saleProb_mem M hM true (a q true) q (has _ _ _) hq
      have hsLq := saleProb_mem M hM false (a q false) q (has _ _ _) hq
      have hsHp := saleProb_mem M hM true (a p true) p (has _ _ _) hp
      have hsLp := saleProb_mem M hM false (a p false) p (has _ _ _) hp
      have hLq : (1 - M.phiH) * M.rhoC q ≤ saleProb M true (a q true) q := by
        unfold saleProb Market.phiVal
        simp only [if_true]
        have := (has (φ k) q true).1
        have := le_trans (hM.rhoC_nonneg q hq) (hM.rhoC_le_rho0 q hq)
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ M.phiH) (has (φ k) q true).1) this]
      have hpabs : p * saleProb M false (a p false) p ≤ Pm := by
        have h1 : p * saleProb M false (a p false) p ≤ |p| * saleProb M false (a p false) p :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hsLp.1
        have h2 : |p| * saleProb M false (a p false) p ≤ |p| :=
          mul_le_of_le_one_right (abs_nonneg _) hsLp.2
        have h3 : |p| ≤ Pm := by
          rw [hPm, abs_le]
          constructor
          · have := neg_abs_le M.pLo; have := hp.1; have := abs_nonneg M.pHi; linarith
          · have := le_abs_self M.pHi; have := hp.2; have := abs_nonneg M.pLo; linarith
        linarith
      simp only [hRv, hx]
      have e1 : q * (μk * saleProb M true (a q true) q + (1 - μk) * saleProb M false (a q false) q)
          ≥ (1 - (1 - μk)) * (q * ((1 - M.phiH) * M.rhoC q)) := by
        have := mul_le_mul_of_nonneg_left hLq hm.1
        have := mul_nonneg (by linarith [hm.2] : (0:ℝ) ≤ 1 - μk) hsLq.1
        nlinarith [mul_le_mul_of_nonneg_left this hq0]
      have e2 : p * (μk * saleProb M true (a p true) p + (1 - μk) * saleProb M false (a p false) p)
          ≤ (1 - μk) * Pm + (1 - (1 - μk)) * (p * saleProb M true (a p true) p) := by
        have := mul_le_mul_of_nonneg_left hpabs (by linarith [hm.2] : (0:ℝ) ≤ 1 - μk)
        nlinarith
      linarith
    have hL : Tendsto (fun k => (1 - (1 - μs (φ k))) * (q * ((1 - M.phiH) * M.rhoC q))) atTop
        (𝓝 ((1 - 0) * (q * ((1 - M.phiH) * M.rhoC q)))) :=
      (tendsto_const_nhds.sub hμφ).mul tendsto_const_nhds
    have hR : Tendsto (fun k => (1 - μs (φ k)) * Pm + (1 - (1 - μs (φ k))) * Rv (x (φ k))) atTop
        (𝓝 (0 * Pm + (1 - 0) * Rv xb)) :=
      (hμφ.mul tendsto_const_nhds).add ((tendsto_const_nhds.sub hμφ).mul hRlim)
    have := le_of_tendsto_of_tendsto' hL hR hk
    simpa using this
  -- (iii) a single-price rule at belief 0 realizes the limit
  obtain ⟨ab, pb⟩ := xb
  obtain ⟨hab, hpb⟩ := hxbK
  set b : ℝ → Bool → ℝ := fun q b' => if q = pb then (if b' then ab else 0) else 0 with hbdef
  have hbv : IsValidRule b := by
    intro q b'
    simp only [hbdef]
    split_ifs
    · exact hab
    · exact ⟨le_refl _, zero_le_one⟩
    · exact ⟨le_refl _, zero_le_one⟩
  have hbs : ∀ q ∈ M.price, q ≠ pb → ∀ b', b q b' = 0 := by
    intro q _ hq b'; simp [hbdef, hq]
  obtain ⟨p', hp'⟩ := exists_myopic M hM b hbv pb hpb hbs 1 ⟨zero_le_one, le_refl _⟩
  have hrev : ∀ q, expRev M 1 b q = q * saleProb M true (b q true) q := by
    intro q; simp [expRev]
  have hsur : ∀ q, expSurplus M 1 b q = surplus M true (b q true) q := by
    intro q; simp [expSurplus]
  have hbpb : b pb true = ab := by simp [hbdef]
  have hR0 : 0 ≤ Rv (ab, pb) := by
    have := hii 0 ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩ (le_refl _)
    simpa using this
  have hpb_max : expRev M 1 b p' ≤ expRev M 1 b pb := by
    rw [hrev, hrev, hbpb]
    by_cases hq : p' = pb
    · rw [hq, hbpb]
    · have hb0 : b p' true = 0 := by simp [hbdef, hq]
      rw [hb0]
      have hval : p' * saleProb M true 0 p' = p' * ((1 - M.phiH) * M.rhoC p') := by
        simp [saleProb, Market.phiVal]
      rw [hval]
      have hRv : Rv (ab, pb) = pb * saleProb M true ab pb := rfl
      rcases le_or_gt 0 p' with h0 | h0
      · have := hii p' hp'.1 h0
        rw [hRv] at this; exact this
      · have hc := hM.rhoC_nonneg p' hp'.1
        have : p' * ((1 - M.phiH) * M.rhoC p') ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h0.le (mul_nonneg (by linarith) hc)
        rw [hRv] at hR0
        linarith
  have heq : expRev M 1 b pb = expRev M 1 b p' := le_antisymm (hp'.2.1 pb hpb) hpb_max
  have hS' := hp'.2.2 pb hpb heq
  have hW : expSurplus M 1 b p' ≤ Wmax M 1 :=
    le_csSup (Wmax_bdd M hM 1 ⟨zero_le_one, le_refl _⟩) ⟨b, p', hbv, hp', rfl⟩
  rw [hsur, hbpb] at hS'
  have hSxb : S (ab, pb) = surplus M true ab pb := rfl
  rw [hSxb] at hi
  linarith

end CPSolL4

open CPSolL4

theorem solution (M : Market) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε) :
    ∃ Cbar : ℝ, 0 ≤ Cbar ∧ ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      co (Wmax M) μ - co (WC M) μ < ε / 2 + Cbar * μ ∧
      co (Wmax M) μ - co (WC M) μ < ε / 2 + Cbar * (1 - μ) := by
  obtain ⟨δ0, hδ0, h0⟩ := usc0 M hM (ε / 8) (by linarith)
  obtain ⟨δ1, hδ1, h1⟩ := usc1 M hM (ε / 8) (by linarith)
  set Bw := max 0 (|M.Wout| + |M.W0 M.pLo| + |M.Wc M.pLo|) with hBw
  have hWle : ∀ x ∈ Set.Icc (0:ℝ) 1, Wmax M x ≤ Bw := fun x hx => Wmax_le M hM x hx
  set w0 := Wmax M 0 with hw0
  set w1 := Wmax M 1 with hw1
  set C1 := (|Bw| + |w0|) / δ0 with hC1
  set C2 := (|Bw| + |w1|) / δ1 with hC2
  have hC1n : 0 ≤ C1 := div_nonneg (by positivity) hδ0.le
  have hC2n : 0 ≤ C2 := div_nonneg (by positivity) hδ1.le
  have hg1 : ∀ x ∈ Set.Icc (0:ℝ) 1, Wmax M x ≤ (w0 + ε / 8) + C1 * x := by
    intro x hx
    by_cases hxd : x ≤ δ0
    · have := h0 x hx hxd
      have : 0 ≤ C1 * x := mul_nonneg hC1n hx.1
      linarith
    · push_neg at hxd
      have hC1d : C1 * δ0 = |Bw| + |w0| := by rw [hC1]; field_simp
      have : C1 * δ0 ≤ C1 * x := mul_le_mul_of_nonneg_left hxd.le hC1n
      have := hWle x hx
      have := le_abs_self Bw
      have := neg_abs_le w0
      linarith
  have hg2 : ∀ x ∈ Set.Icc (0:ℝ) 1, Wmax M x ≤ (w1 + ε / 8 + C2) + (-C2) * x := by
    intro x hx
    by_cases hxd : 1 - δ1 ≤ x
    · have := h1 x hx hxd
      have : 0 ≤ C2 * (1 - x) := mul_nonneg hC2n (by linarith [hx.2])
      linarith
    · push_neg at hxd
      have hC2d : C2 * δ1 = |Bw| + |w1| := by rw [hC2]; field_simp
      have : C2 * δ1 ≤ C2 * (1 - x) := mul_le_mul_of_nonneg_left (by linarith) hC2n
      have := hWle x hx
      have := le_abs_self Bw
      have := neg_abs_le w1
      linarith
  have hWCB : ∀ x ∈ Set.Icc (0:ℝ) 1, WC M x ≤ Bw := fun x hx => WC_le M hM x hx
  refine ⟨C1 + C2 + |w0 - w1|, by positivity, ?_⟩
  intro μ hμ
  have hA := co_le_affine (Wmax M) _ _ hg1 μ hμ
  have hB := co_le_affine (Wmax M) _ _ hg2 μ hμ
  have hC := chord_le_co (WC M) Bw hWCB μ hμ
  rw [WC_eq_Wmax_zero, WC_eq_Wmax_one] at hC
  rw [← hw0, ← hw1] at hC
  obtain ⟨hμ0, hμ1⟩ := hμ
  have habs1 : μ * (w0 - w1) ≤ μ * |w0 - w1| := mul_le_mul_of_nonneg_left (le_abs_self _) hμ0
  have habs2 : (1 - μ) * (w1 - w0) ≤ (1 - μ) * |w0 - w1| := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    rw [abs_sub_comm]; exact le_abs_self _
  have hm1 : 0 ≤ μ * C2 := mul_nonneg hμ0 hC2n
  have hm2 : 0 ≤ (1 - μ) * C1 := mul_nonneg (by linarith) hC1n
  constructor
  · nlinarith
  · nlinarith
