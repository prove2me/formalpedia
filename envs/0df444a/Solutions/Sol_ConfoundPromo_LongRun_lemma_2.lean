-- Prove2me | solution 1 for ConfoundPromo.LongRun.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T08:30:37.191479+00:00
-- url     : https://prove2.me/submissions/82a8d1f5-0646-4074-bf1b-aabb4d014ea2

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

open ConfoundPromo.LongRun
open Finset
open Filter Topology

namespace CPSolL2

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

end CPSolL2

namespace CPSolL2

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


end CPSolL2

namespace CPSolL2

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

end CPSolL2

namespace CPSolL2

lemma zero_rule_myopic (M : Market) (hM : M.Standing) (μ' : ℝ) (hμ' : μ' ∈ Set.Icc (0:ℝ) 1)
    (p' : ℝ) (hp' : p' ∈ M.price) (hmax : ∀ q ∈ M.price, q * M.rhoC q ≤ p' * M.rhoC p') :
    IsMyopicChoice M μ' (fun _ _ => 0) p' := by
  have hφL := hM.phiL_pos
  have hφLH := hM.phiL_lt_phiH
  have hφH := hM.phiH_lt_one
  obtain ⟨h0, h1⟩ := hμ'
  set cc := μ' * (1 - M.phiH) + (1 - μ') * (1 - M.phiL) with hcc
  have hcpos : 0 < cc := by nlinarith
  have hrev : ∀ q, expRev M μ' (fun _ _ => 0) q = cc * (q * M.rhoC q) := by
    intro q; simp only [expRev, saleProb, Market.phiVal, if_true, Bool.false_eq_true, if_false,
      mul_zero, zero_mul, zero_add, hcc]; ring
  refine ⟨hp', ?_, ?_⟩
  · intro q hq
    rw [hrev, hrev]
    exact mul_le_mul_of_nonneg_left (hmax q hq) hcpos.le
  · intro q hq heq
    rw [hrev, hrev] at heq
    have heq' : q * M.rhoC q = p' * M.rhoC p' := by
      have := mul_left_cancel₀ hcpos.ne' heq; exact this
    by_cases hqp : q = p'
    · rw [hqp]
    · exfalso
      have hs := hM.revC_strictConcave.2 hq hp' hqp (by norm_num : (0:ℝ) < 1/2)
        (by norm_num : (0:ℝ) < 1/2) (by norm_num)
      have hm : (1/2 : ℝ) • q + (1/2 : ℝ) • p' ∈ M.price :=
        (convex_Icc M.pLo M.pHi) hq hp' (by norm_num) (by norm_num) (by norm_num)
      have := hmax _ hm
      simp only [smul_eq_mul] at hs this
      linarith

lemma conc_lower (g : ℝ → ℝ) (hg : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) g) (B : ℝ)
    (hB : ∀ x ∈ Set.Icc (0:ℝ) 1, |g x| ≤ B) (μ : ℝ) (hμ : μ ∈ Set.Icc (0:ℝ) 1)
    (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    g μ - 2 * B * |x - μ| * (1 / μ + 1 / (1 - μ)) ≤ g x := by
  have hBμ := hB μ hμ
  have hB0 := hB 0 ⟨le_refl _, zero_le_one⟩
  have hB1 := hB 1 ⟨zero_le_one, le_refl _⟩
  have hBn : 0 ≤ B := le_trans (abs_nonneg _) hBμ
  obtain ⟨hμ0, hμ1⟩ := hμ
  obtain ⟨hx0, hx1⟩ := hx
  have hinv0 : 0 ≤ 1 / μ := by positivity
  have hinv1 : 0 ≤ 1 / (1 - μ) := one_div_nonneg.mpr (by linarith)
  rcases le_total μ x with hle | hle
  · rcases eq_or_lt_of_le hμ1 with h1 | h1
    · have : x = μ := by linarith
      subst this; simp
    · have hd : 0 < 1 - μ := by linarith
      set lam := (1 - x) / (1 - μ) with hlam
      have hl0 : 0 ≤ lam := div_nonneg (by linarith) hd.le
      have hl1 : lam ≤ 1 := by rw [div_le_one hd]; linarith
      have hconv := hg.2 ⟨hμ0, hμ1⟩ ⟨zero_le_one, le_refl _⟩ hl0 (by linarith : 0 ≤ 1 - lam)
        (by ring)
      simp only [smul_eq_mul] at hconv
      have hxeq : lam * μ + (1 - lam) * 1 = x := by rw [hlam]; field_simp; ring
      rw [hxeq] at hconv
      have h1l : 1 - lam = (x - μ) / (1 - μ) := by rw [hlam]; field_simp; ring
      have habs : |x - μ| = x - μ := abs_of_nonneg (by linarith)
      have hgd : g μ - g 1 ≤ 2 * B := by
        have := abs_le.mp hBμ; have := abs_le.mp hB1; linarith
      have key : (1 - lam) * (g μ - g 1) ≤ 2 * B * |x - μ| * (1 / μ + 1 / (1 - μ)) := by
        rw [h1l, habs]
        have : (x - μ) / (1 - μ) * (g μ - g 1) ≤ (x - μ) / (1 - μ) * (2 * B) :=
          mul_le_mul_of_nonneg_left hgd (div_nonneg (by linarith) hd.le)
        have h2 : (x - μ) / (1 - μ) * (2 * B) = 2 * B * (x - μ) * (1 / (1 - μ)) := by ring
        have h3 : 2 * B * (x - μ) * (1 / (1 - μ)) ≤ 2 * B * (x - μ) * (1 / μ + 1 / (1 - μ)) := by
          apply mul_le_mul_of_nonneg_left _ (by nlinarith)
          linarith
        linarith
      nlinarith
  · rcases eq_or_lt_of_le hμ0 with h0 | h0
    · have : x = μ := by linarith
      subst this; simp
    · set lam := x / μ with hlam
      have hl0 : 0 ≤ lam := div_nonneg hx0 h0.le
      have hl1 : lam ≤ 1 := by rw [div_le_one h0]; linarith
      have hconv := hg.2 ⟨hμ0, hμ1⟩ ⟨le_refl _, zero_le_one⟩ hl0 (by linarith : 0 ≤ 1 - lam)
        (by ring)
      simp only [smul_eq_mul] at hconv
      have hxeq : lam * μ + (1 - lam) * 0 = x := by rw [hlam]; field_simp; ring
      rw [hxeq] at hconv
      have h1l : 1 - lam = (μ - x) / μ := by rw [hlam]; field_simp
      have habs : |x - μ| = μ - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      have hgd : g μ - g 0 ≤ 2 * B := by
        have := abs_le.mp hBμ; have := abs_le.mp hB0; linarith
      have key : (1 - lam) * (g μ - g 0) ≤ 2 * B * |x - μ| * (1 / μ + 1 / (1 - μ)) := by
        rw [h1l, habs]
        have : (μ - x) / μ * (g μ - g 0) ≤ (μ - x) / μ * (2 * B) :=
          mul_le_mul_of_nonneg_left hgd (div_nonneg (by linarith) h0.le)
        have h2 : (μ - x) / μ * (2 * B) = 2 * B * (μ - x) * (1 / μ) := by ring
        have h3 : 2 * B * (μ - x) * (1 / μ) ≤ 2 * B * (μ - x) * (1 / μ + 1 / (1 - μ)) := by
          apply mul_le_mul_of_nonneg_left _ (by nlinarith)
          linarith
        linarith
      nlinarith

end CPSolL2

open CPSolL2

set_option maxHeartbeats 1000000 in
theorem solution (M : Market) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ ∈ Set.Icc (0 : ℝ) 1, ∀ (a : ℝ → Bool → ℝ) (p : ℝ),
      IsValidRule a →
      (∃ pbar ∈ M.price, ∀ q ∈ M.price, q ≠ pbar → ∀ b, a q b = 0) →
      IsMyopicChoice M μ a p →
      co (WC M) μ + ε < expSurplus M μ a p →
      δ < |saleProb M true (a p true) p - saleProb M false (a p false) p| := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ k : ℕ, ∃ μ ∈ Set.Icc (0:ℝ) 1, ∃ (a : ℝ → Bool → ℝ) (p : ℝ), IsValidRule a ∧
      (∃ pbar ∈ M.price, ∀ q ∈ M.price, q ≠ pbar → ∀ b, a q b = 0) ∧
      IsMyopicChoice M μ a p ∧ co (WC M) μ + ε < expSurplus M μ a p ∧
      |saleProb M true (a p true) p - saleProb M false (a p false) p| ≤ 1 / ((k:ℝ) + 1) :=
    fun k => hcon _ (by positivity)
  choose μs hμs as ps has hsing hms hgt hsep using hseq
  have hφL := hM.phiL_pos
  have hφLH := hM.phiL_lt_phiH
  have hφH := hM.phiH_lt_one
  -- bounds on co(W^C)
  set Bw := max 0 (|M.Wout| + |M.W0 M.pLo| + |M.Wc M.pLo|) with hBw
  have hWCB : ∀ x ∈ Set.Icc (0:ℝ) 1, WC M x ≤ Bw := fun x hx => WC_le M hM x hx
  have hconc : ConcaveOn ℝ (Set.Icc (0:ℝ) 1) (co (WC M)) := co_concave (WC M) Bw hWCB
  set B := |Bw| + |WC M 0| + |WC M 1| with hBdef
  have hcoB : ∀ x ∈ Set.Icc (0:ℝ) 1, |co (WC M) x| ≤ B := by
    intro x hx
    have hup := co_le_affine (WC M) Bw 0 (fun y hy => by simpa using hWCB y hy) x hx
    have hlo := chord_le_co (WC M) Bw hWCB x hx
    rw [abs_le]
    constructor
    · have h1 : (1 - x) * WC M 0 ≥ -(1 - x) * |WC M 0| := by
        have := neg_abs_le (WC M 0); nlinarith [hx.2]
      have h2 : x * WC M 1 ≥ -x * |WC M 1| := by
        have := neg_abs_le (WC M 1); nlinarith [hx.1]
      have h3 : (1 - x) * |WC M 0| ≤ |WC M 0| := by nlinarith [abs_nonneg (WC M 0), hx.1]
      have h4 : x * |WC M 1| ≤ |WC M 1| := by nlinarith [abs_nonneg (WC M 1), hx.2]
      have := abs_nonneg Bw
      linarith
    · have := le_abs_self Bw
      have := abs_nonneg (WC M 0); have := abs_nonneg (WC M 1)
      linarith
  -- compactness
  set K : Set (ℝ × ℝ × ℝ × ℝ) :=
    Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ M.price)) with hK
  set x : ℕ → ℝ × ℝ × ℝ × ℝ :=
    fun k => (μs k, as k (ps k) true, as k (ps k) false, ps k) with hx
  have hxK : ∀ k, x k ∈ K := fun k => ⟨hμs k, has k _ true, has k _ false, (hms k).1⟩
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  obtain ⟨xb, hxbK, φ, hφ, hlim⟩ := hKc.tendsto_subseq hxK
  have hW0c : ContinuousOn M.W0 M.price := by
    obtain ⟨L, hL⟩ := hM.W0_lipschitz; exact hL.continuousOn
  have hWcc : ContinuousOn M.Wc M.price := by
    obtain ⟨L, hL⟩ := hM.Wc_lipschitz; exact hL.continuousOn
  have hr0c : ContinuousOn M.rho0 M.price := by
    obtain ⟨L, hL⟩ := hM.rho0_lipschitz; exact hL.continuousOn
  have hrcc : ContinuousOn M.rhoC M.price := by
    obtain ⟨L, hL⟩ := hM.rhoC_lipschitz; exact hL.continuousOn
  have hp4 : ContinuousOn (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.2) K :=
    continuous_snd.comp (continuous_snd.comp continuous_snd) |>.continuousOn
  have hmaps : Set.MapsTo (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.2) K M.price := fun z hz => hz.2.2.2
  have hμc : ContinuousOn (fun z : ℝ × ℝ × ℝ × ℝ => z.1) K := continuous_fst.continuousOn
  have haHc : ContinuousOn (fun z : ℝ × ℝ × ℝ × ℝ => z.2.1) K :=
    (continuous_fst.comp continuous_snd).continuousOn
  have haLc : ContinuousOn (fun z : ℝ × ℝ × ℝ × ℝ => z.2.2.1) K :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).continuousOn
  have hW0' : ContinuousOn (fun z : ℝ × ℝ × ℝ × ℝ => M.W0 z.2.2.2) K := hW0c.comp hp4 hmaps
  have hWc' : ContinuousOn (fun z : ℝ × ℝ × ℝ × ℝ => M.Wc z.2.2.2) K := hWcc.comp hp4 hmaps
  have hr0' : ContinuousOn (fun z : ℝ × ℝ × ℝ × ℝ => M.rho0 z.2.2.2) K := hr0c.comp hp4 hmaps
  have hrc' : ContinuousOn (fun z : ℝ × ℝ × ℝ × ℝ => M.rhoC z.2.2.2) K := hrcc.comp hp4 hmaps
  set FS : ℝ × ℝ × ℝ × ℝ → ℝ := fun z => z.1 * surplus M true z.2.1 z.2.2.2 +
    (1 - z.1) * surplus M false z.2.2.1 z.2.2.2 with hFS
  set FD : ℝ × ℝ × ℝ × ℝ → ℝ := fun z => saleProb M true z.2.1 z.2.2.2 -
    saleProb M false z.2.2.1 z.2.2.2 with hFD
  set FR : ℝ × ℝ × ℝ × ℝ → ℝ := fun z => z.2.2.2 * (z.1 * saleProb M true z.2.1 z.2.2.2 +
    (1 - z.1) * saleProb M false z.2.2.1 z.2.2.2) with hFR
  have hsurc : ∀ (b : Bool) (f : ℝ × ℝ × ℝ × ℝ → ℝ), ContinuousOn f K →
      ContinuousOn (fun z => surplus M b (f z) z.2.2.2) K := by
    intro b f hf
    simp only [surplus]
    exact (continuousOn_const.mul (continuousOn_const.add (hf.mul (hW0'.sub continuousOn_const)))).add
      (continuousOn_const.mul hWc')
  have hsalec : ∀ (b : Bool) (f : ℝ × ℝ × ℝ × ℝ → ℝ), ContinuousOn f K →
      ContinuousOn (fun z => saleProb M b (f z) z.2.2.2) K := by
    intro b f hf
    simp only [saleProb]
    exact ((continuousOn_const.mul hf).mul hr0').add (continuousOn_const.mul hrc')
  have hFSc : ContinuousOn FS K :=
    (hμc.mul (hsurc true _ haHc)).add ((continuousOn_const.sub hμc).mul (hsurc false _ haLc))
  have hFDc : ContinuousOn FD K := (hsalec true _ haHc).sub (hsalec false _ haLc)
  have hFRc : ContinuousOn FR K :=
    hp4.mul ((hμc.mul (hsalec true _ haHc)).add ((continuousOn_const.sub hμc).mul (hsalec false _ haLc)))
  have hxφ : Tendsto (fun k => x (φ k)) atTop (𝓝[K] xb) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun k => hxK _)⟩
  have hFSlim : Tendsto (fun k => FS (x (φ k))) atTop (𝓝 (FS xb)) := (hFSc xb hxbK).tendsto.comp hxφ
  have hFDlim : Tendsto (fun k => FD (x (φ k))) atTop (𝓝 (FD xb)) := (hFDc xb hxbK).tendsto.comp hxφ
  have hFRlim : Tendsto (fun k => FR (x (φ k))) atTop (𝓝 (FR xb)) := (hFRc xb hxbK).tendsto.comp hxφ
  have hμlim : Tendsto (fun k => μs (φ k)) atTop (𝓝 xb.1) :=
    ((continuous_fst.tendsto xb).comp hlim)
  obtain ⟨μb, aHb, aLb, pb⟩ := xb
  obtain ⟨hμb, haHb, haLb, hpb⟩ := hxbK
  simp only at hμlim
  -- values along the sequence
  have hFSk : ∀ k, FS (x k) = expSurplus M (μs k) (as k) (ps k) := by intro k; rfl
  have hFDk : ∀ k, FD (x k) = saleProb M true (as k (ps k) true) (ps k) -
      saleProb M false (as k (ps k) false) (ps k) := by intro k; rfl
  have hFRk : ∀ k, FR (x k) = expRev M (μs k) (as k) (ps k) := by intro k; rfl
  -- (i) limit surplus exceeds co(W^C)(μb) + ε
  set Kc := 1 / μb + 1 / (1 - μb) with hKc
  have hi : co (WC M) μb + ε ≤ FS (μb, aHb, aLb, pb) := by
    have hk : ∀ k, co (WC M) μb - 2 * B * |μs (φ k) - μb| * Kc + ε ≤ FS (x (φ k)) := by
      intro k
      have h1 := conc_lower (co (WC M)) hconc B hcoB μb hμb (μs (φ k)) (hμs _)
      rw [hFSk]
      have := hgt (φ k)
      linarith
    have hT : Tendsto (fun k => co (WC M) μb - 2 * B * |μs (φ k) - μb| * Kc + ε) atTop
        (𝓝 (co (WC M) μb - 2 * B * |μb - μb| * Kc + ε)) := by
      apply Tendsto.add_const
      apply Tendsto.sub tendsto_const_nhds
      apply Tendsto.mul_const
      apply Tendsto.const_mul
      exact (continuous_abs.tendsto _).comp (hμlim.sub_const μb)
    simp only [sub_self, abs_zero, mul_zero, zero_mul, sub_zero] at hT
    exact le_of_tendsto_of_tendsto' hT hFSlim hk
  -- (ii) confounding in the limit
  have hii : FD (μb, aHb, aLb, pb) = 0 := by
    have h0 : Tendsto (fun k => FD (x (φ k))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
      · intro k; exact abs_nonneg _
      · intro k; simp only [Function.comp]; rw [hFDk]; exact hsep (φ k)
    exact tendsto_nhds_unique hFDlim h0
  -- (iii) revenue dominance in the limit
  set cc : ℝ → ℝ := fun μ => μ * (1 - M.phiH) + (1 - μ) * (1 - M.phiL) with hccdef
  have hiii : ∀ q ∈ M.price, 0 ≤ q → q * (cc μb * M.rhoC q) ≤ FR (μb, aHb, aLb, pb) := by
    intro q hq hq0
    have hk : ∀ k, q * (cc (μs (φ k)) * M.rhoC q) ≤ FR (x (φ k)) := by
      intro k
      rw [hFRk]
      have hmy := (hms (φ k)).2.1 q hq
      refine le_trans ?_ hmy
      unfold expRev
      have hm := hμs (φ k)
      have hsH : (1 - M.phiH) * M.rhoC q ≤ saleProb M true (as (φ k) q true) q := by
        unfold saleProb Market.phiVal; simp only [if_true]
        have := (has (φ k) q true).1
        have := le_trans (hM.rhoC_nonneg q hq) (hM.rhoC_le_rho0 q hq)
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ M.phiH) (has (φ k) q true).1) this]
      have hsL : (1 - M.phiL) * M.rhoC q ≤ saleProb M false (as (φ k) q false) q := by
        unfold saleProb Market.phiVal; simp only [Bool.false_eq_true, if_false]
        have := (has (φ k) q false).1
        have := le_trans (hM.rhoC_nonneg q hq) (hM.rhoC_le_rho0 q hq)
        nlinarith [mul_nonneg (mul_nonneg hφL.le (has (φ k) q false).1) this]
      simp only [hccdef]
      apply mul_le_mul_of_nonneg_left _ hq0
      nlinarith [mul_le_mul_of_nonneg_left hsH hm.1,
        mul_le_mul_of_nonneg_left hsL (by linarith [hm.2] : (0:ℝ) ≤ 1 - μs (φ k))]
    have hT : Tendsto (fun k => q * (cc (μs (φ k)) * M.rhoC q)) atTop
        (𝓝 (q * (cc μb * M.rhoC q))) := by
      apply Tendsto.const_mul
      apply Tendsto.mul_const
      simp only [hccdef]
      exact (hμlim.mul_const _).add ((tendsto_const_nhds.sub hμlim).mul_const _)
    exact le_of_tendsto_of_tendsto' hT hFRlim hk
  -- (iv) realization at μb
  set b : ℝ → Bool → ℝ := fun q bb => if q = pb then (if bb then aHb else aLb) else 0 with hbdef
  have hbv : IsValidRule b := by
    intro q bb
    simp only [hbdef]
    split_ifs
    · exact haHb
    · exact haLb
    · exact ⟨le_refl _, zero_le_one⟩
  have hbs : ∀ q ∈ M.price, q ≠ pb → ∀ bb, b q bb = 0 := by
    intro q _ hq bb; simp [hbdef, hq]
  obtain ⟨p', hp'⟩ := exists_myopic M hM b hbv pb hpb hbs μb hμb
  have hbpb : ∀ bb, b pb bb = if bb then aHb else aLb := by intro bb; simp [hbdef]
  have hrevpb : expRev M μb b pb = FR (μb, aHb, aLb, pb) := by
    simp only [expRev, hbpb, if_true, Bool.false_eq_true, if_false, hFR]
  have hsurpb : expSurplus M μb b pb = FS (μb, aHb, aLb, pb) := by
    simp only [expSurplus, hbpb, if_true, Bool.false_eq_true, if_false, hFS]
  have hcpos : 0 < cc μb := by simp only [hccdef]; nlinarith [hμb.1, hμb.2]
  have hrevU : ∀ q, q ≠ pb → expRev M μb b q = q * (cc μb * M.rhoC q) := by
    intro q hq
    simp only [expRev, hbdef, if_neg hq, saleProb, Market.phiVal, if_true, Bool.false_eq_true,
      if_false, hccdef]
    ring
  have hFR0 : 0 ≤ FR (μb, aHb, aLb, pb) := by
    have := hiii 0 ⟨hM.pLo_nonpos, hM.pHi_nonneg⟩ (le_refl _)
    simpa using this
  have hcoWC : WC M μb ≤ co (WC M) μb := le_co (WC M) Bw hWCB μb hμb
  by_cases hpp : p' = pb
  · -- confounding myopic choice: value at most W^C
    have hconf : IsConfoundingChoice M μb b pb := by
      intro y
      have hl : likelihood M true (b pb true) pb y = likelihood M false (b pb false) pb y := by
        have h0 : saleProb M true aHb pb = saleProb M false aLb pb := by
          have := hii; simp only [hFD] at this; linarith
        rw [hbpb, hbpb]; simp only [if_true, Bool.false_eq_true, if_false]
        cases y <;> simp [likelihood, h0]
      rw [hl]; exact bayes_same _ _
    have hmy' : IsMyopicChoice M μb b pb := hpp ▸ hp'
    have hbdd : BddAbove {v | ∃ (a : ℝ → Bool → ℝ) (p : ℝ), IsValidRule a ∧
        IsMyopicChoice M μb a p ∧ IsConfoundingChoice M μb a p ∧ v = expSurplus M μb a p} := by
      obtain ⟨B', hB'⟩ := Wmax_bdd M hM μb hμb
      exact ⟨B', fun v ⟨a, p, ha, hm, _, hv⟩ => hB' ⟨a, p, ha, hm, hv⟩⟩
    have hle : expSurplus M μb b pb ≤ WC M μb := le_csSup hbdd ⟨b, pb, hbv, hmy', hconf, rfl⟩
    rw [hsurpb] at hle
    linarith
  · -- the alternative p' is unpromoted and ties
    have hge : expRev M μb b p' ≤ expRev M μb b pb := by
      rw [hrevpb, hrevU p' hpp]
      rcases le_or_gt 0 p' with h0 | h0
      · exact hiii p' hp'.1 h0
      · have hc := hM.rhoC_nonneg p' hp'.1
        have : p' * (cc μb * M.rhoC p') ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h0.le (mul_nonneg hcpos.le hc)
        linarith
    have heq : expRev M μb b pb = expRev M μb b p' := le_antisymm (hp'.2.1 pb hpb) hge
    have hS := hp'.2.2 pb hpb heq
    -- p' maximizes q ρc(q)
    have hmaxU : ∀ q ∈ M.price, q * M.rhoC q ≤ p' * M.rhoC p' := by
      intro q hq
      have key : q * (cc μb * M.rhoC q) ≤ p' * (cc μb * M.rhoC p') := by
        by_cases hqb : q = pb
        · rw [hqb]
          rcases le_or_gt 0 pb with h0 | h0
          · -- promotion only adds revenue at a nonnegative price
            have : pb * (cc μb * M.rhoC pb) ≤ expRev M μb b pb := by
              rw [hrevpb]; exact hiii pb hpb h0
            rw [← hrevU p' hpp, ← heq]; exact this
          · have hc := hM.rhoC_nonneg pb hpb
            have h1 : pb * (cc μb * M.rhoC pb) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg h0.le (mul_nonneg hcpos.le hc)
            rw [← hrevU p' hpp, ← heq, hrevpb]; linarith
        · rw [← hrevU q hqb, ← hrevU p' hpp]; exact hp'.2.1 q hq
      have h2 : cc μb * (q * M.rhoC q) ≤ cc μb * (p' * M.rhoC p') := by
        have e1 : cc μb * (q * M.rhoC q) = q * (cc μb * M.rhoC q) := by ring
        have e2 : cc μb * (p' * M.rhoC p') = p' * (cc μb * M.rhoC p') := by ring
        rw [e1, e2]; exact key
      exact le_of_mul_le_mul_left h2 hcpos
    have hz : IsValidRule (fun _ _ => (0:ℝ)) := fun _ _ => ⟨le_refl _, zero_le_one⟩
    have hmy1 := zero_rule_myopic M hM 1 ⟨zero_le_one, le_refl _⟩ p' hp'.1 hmaxU
    have hmy0 := zero_rule_myopic M hM 0 ⟨le_refl _, zero_le_one⟩ p' hp'.1 hmaxU
    have hW1 : expSurplus M 1 (fun _ _ => 0) p' ≤ Wmax M 1 :=
      le_csSup (Wmax_bdd M hM 1 ⟨zero_le_one, le_refl _⟩) ⟨_, _, hz, hmy1, rfl⟩
    have hW0 : expSurplus M 0 (fun _ _ => 0) p' ≤ Wmax M 0 :=
      le_csSup (Wmax_bdd M hM 0 ⟨le_refl _, zero_le_one⟩) ⟨_, _, hz, hmy0, rfl⟩
    have hb0 : ∀ bb, b p' bb = 0 := fun bb => by simp [hbdef, hpp]
    have hSp' : expSurplus M μb b p' =
        μb * expSurplus M 1 (fun _ _ => 0) p' + (1 - μb) * expSurplus M 0 (fun _ _ => 0) p' := by
      simp only [expSurplus, hb0]; ring
    have hch := chord_le_co (WC M) Bw hWCB μb hμb
    rw [WC_eq_Wmax_zero, WC_eq_Wmax_one] at hch
    rw [hsurpb, hSp'] at hS
    have := mul_le_mul_of_nonneg_left hW1 hμb.1
    have := mul_le_mul_of_nonneg_left hW0 (by linarith [hμb.2] : (0:ℝ) ≤ 1 - μb)
    linarith
