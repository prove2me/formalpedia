-- Prove2me | solution 1 for ConfoundPromo.LongRun.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T08:23:31.59906+00:00
-- url     : https://prove2.me/submissions/2ebab5dc-1ec7-4c1f-972f-1fc6b88b4c4d

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model
import Theorems.Thm_ConfoundPromo_LongRun_lemma_2

open ConfoundPromo.LongRun
open Finset

namespace CPSolL3

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

end CPSolL3

namespace CPSolL3

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

/-! ## Histories -/

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

/-! ## Path-probability machinery for a fixed state and signal -/

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

end CPSolL3

namespace CPSolL3

open scoped Classical

/-! ## Re-indexing a sum over excess periods by the hitting index -/

noncomputable def cnt {T : ℕ} (P : Fin T → Prop) (t : Fin T) : ℕ :=
  (univ.filter (fun t' : Fin T => t' ≤ t ∧ P t')).card

noncomputable def reach {T : ℕ} (P : Fin T → Prop) (m : ℕ) : Finset (Fin T) :=
  univ.filter (fun t : Fin T => m ≤ cnt P t)

lemma reindex {T : ℕ} (P : Fin T → Prop) (v : Fin T → ℝ) :
    ∑ t, (if P t then v t else 0) =
      ∑ m ∈ Finset.Icc 1 T, (if h : (reach P m).Nonempty then v ((reach P m).min' h) else 0) := by
  set E := univ.filter P with hE
  have hL : ∑ t, (if P t then v t else 0) = ∑ t ∈ E, v t := (Finset.sum_filter _ _).symm
  have hcntle : ∀ t, cnt P t ≤ E.card := by
    intro t
    apply Finset.card_le_card
    intro t' ht'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht'
    rw [hE, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ht'.2⟩
  have hlt : ∀ t1 t2 : Fin T, t1 < t2 → P t2 → cnt P t1 < cnt P t2 := by
    intro t1 t2 h12 hP
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨t2, ?_, ?_⟩
      · simp [hP]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h; exact absurd h (not_le.mpr h12)
    · intro t' ht'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht' ⊢
      exact ⟨le_trans ht'.1 h12.le, ht'.2⟩
  have hge1 : ∀ t, P t → 1 ≤ cnt P t := by
    intro t hP
    apply Finset.card_pos.mpr
    exact ⟨t, by simp [hP]⟩
  have hmin : ∀ t ∈ E, ∀ h : (reach P (cnt P t)).Nonempty, (reach P (cnt P t)).min' h = t := by
    intro t ht h
    have hPt : P t := by simpa [hE] using ht
    apply le_antisymm
    · apply Finset.min'_le
      simp [reach]
    · apply Finset.le_min'
      intro t' ht'
      by_contra hc
      push_neg at hc
      have := hlt t' t hc hPt
      simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at ht'
      omega
  have hne : ∀ m ∈ Finset.Icc 1 E.card, (reach P m).Nonempty := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hEne : E.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨E.max' hEne, ?_⟩
    have : cnt P (E.max' hEne) = E.card := by
      unfold cnt
      congr 1
      ext t'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hE]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨Finset.le_max' _ _ (by simp [hE, h]), h⟩
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hgood : ∀ m ∈ Finset.Icc 1 E.card, ∀ h : (reach P m).Nonempty,
      P ((reach P m).min' h) ∧ cnt P ((reach P m).min' h) = m := by
    intro m hm h
    rw [Finset.mem_Icc] at hm
    set ts := (reach P m).min' h with hts
    have hts_mem : m ≤ cnt P ts := by
      have := Finset.min'_mem (reach P m) h
      rw [← hts] at this
      simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    set A := univ.filter (fun t' : Fin T => t' < ts ∧ P t') with hA
    have hAc : A.card < m := by
      by_cases hAe : A.Nonempty
      · set t'' := A.max' hAe
        have ht''A := Finset.max'_mem A hAe
        simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at ht''A
        have hcnt : cnt P t'' = A.card := by
          unfold cnt
          congr 1
          ext t'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA]
          constructor
          · intro h'; exact ⟨lt_of_le_of_lt h'.1 ht''A.1, h'.2⟩
          · intro h'; exact ⟨Finset.le_max' _ _ (by simp [hA, h']), h'.2⟩
        have hnot : t'' ∉ reach P m := by
          intro hmem
          have := Finset.min'_le _ _ hmem
          rw [← hts] at this
          exact absurd ht''A.1 (not_lt.mpr this)
        simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot
        omega
      · rw [Finset.not_nonempty_iff_eq_empty] at hAe
        rw [hAe, Finset.card_empty]; omega
    by_cases hP : P ts
    · have hc : cnt P ts = A.card + 1 := by
        unfold cnt
        have : univ.filter (fun t' : Fin T => t' ≤ ts ∧ P t') = insert ts A := by
          ext t'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hA]
          constructor
          · intro h'
            rcases eq_or_lt_of_le h'.1 with he | hl
            · left; exact he
            · right; exact ⟨hl, h'.2⟩
          · rintro (he | h')
            · rw [he]; exact ⟨le_refl _, hP⟩
            · exact ⟨h'.1.le, h'.2⟩
        rw [this, Finset.card_insert_of_notMem]
        simp [hA]
      exact ⟨hP, by omega⟩
    · exfalso
      have hc : cnt P ts = A.card := by
        unfold cnt
        congr 1
        ext t'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA]
        constructor
        · intro h'
          rcases eq_or_lt_of_le h'.1 with he | hl
          · exact absurd (he ▸ h'.2) hP
          · exact ⟨hl, h'.2⟩
        · intro h'; exact ⟨h'.1.le, h'.2⟩
      omega
  have hEcard : E.card ≤ T := by
    have := Finset.card_le_univ E
    simpa using this
  rw [hL]
  have hR : ∑ m ∈ Finset.Icc 1 T, (if h : (reach P m).Nonempty then v ((reach P m).min' h) else 0) =
      ∑ m ∈ Finset.Icc 1 E.card,
        (if h : (reach P m).Nonempty then v ((reach P m).min' h) else 0) := by
    symm
    apply Finset.sum_subset
    · intro m hm
      rw [Finset.mem_Icc] at hm ⊢
      omega
    · intro m hm hm'
      rw [Finset.mem_Icc] at hm hm'
      have hempty : ¬ (reach P m).Nonempty := by
        rintro ⟨t, ht⟩
        simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        have := hcntle t
        omega
      rw [dif_neg hempty]
  rw [hR]
  refine Finset.sum_bij' (fun t _ => cnt P t) (fun m hm => (reach P m).min' (hne m hm))
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    have hPt : P t := by simpa [hE] using ht
    rw [Finset.mem_Icc]
    exact ⟨hge1 t hPt, hcntle t⟩
  · intro m hm
    have := (hgood m hm (hne m hm)).1
    simp [hE, this]
  · intro t ht
    exact hmin t ht _
  · intro m hm
    exact (hgood m hm (hne m hm)).2
  · intro t ht
    have hPt : P t := by simpa [hE] using ht
    have hn : (reach P (cnt P t)).Nonempty := ⟨t, by simp [reach]⟩
    rw [dif_pos hn, hmin t ht hn]

lemma geom_bound (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∀ T : ℕ, ∑ m ∈ Finset.Icc 1 T, r ^ m ≤ r / (1 - r) := by
  have key : ∀ T : ℕ, (1 - r) * ∑ m ∈ Finset.Icc 1 T, r ^ m = r - r ^ (T + 1) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
      ring
  intro T
  rw [le_div_iff₀ (by linarith), mul_comm, key]
  have : 0 ≤ r ^ (T + 1) := pow_nonneg hr0 _
  linarith

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

end CPSolL3

open CPSolL3


namespace CPSolL3

open scoped Classical

/-! ## Bhattacharyya coefficient bounds -/

lemma sqrt_mul_le_add (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x * y) ≤ (x + y) / 2 := by
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith [sq_nonneg (x - y)]

lemma bc_le_one (p q : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    √(p * q) + √((1 - p) * (1 - q)) ≤ 1 := by
  have h1 := sqrt_mul_le_add p q hp.1 hq.1
  have h2 := sqrt_mul_le_add (1 - p) (1 - q) (by linarith [hp.2]) (by linarith [hq.2])
  linarith

lemma bc_le (p q δ : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) (hq : q ∈ Set.Icc (0:ℝ) 1) (hδ0 : 0 ≤ δ)
    (hδ : δ < |p - q|) : √(p * q) + √((1 - p) * (1 - q)) ≤ 1 - δ ^ 2 / 8 := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  set a := √p with ha
  set b := √q with hb
  set a' := √(1 - p) with ha'
  set b' := √(1 - q) with hb'
  have ha2 : a ^ 2 = p := Real.sq_sqrt hp0
  have hb2 : b ^ 2 = q := Real.sq_sqrt hq0
  have ha'2 : a' ^ 2 = 1 - p := Real.sq_sqrt (by linarith)
  have hb'2 : b' ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have hab : √(p * q) = a * b := Real.sqrt_mul hp0 q
  have hab' : √((1 - p) * (1 - q)) = a' * b' := Real.sqrt_mul (by linarith) (1 - q)
  rw [hab, hab']
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hkey : (p - q) ^ 2 = (a - b) ^ 2 * (a + b) ^ 2 := by
    rw [← ha2, ← hb2]; ring
  have hsum : (a + b) ^ 2 ≤ 4 := by nlinarith [sq_nonneg (a - b)]
  have hpq : (p - q) ^ 2 ≤ 4 * (a - b) ^ 2 := by
    rw [hkey]; nlinarith [sq_nonneg (a - b)]
  have hδ2 : δ ^ 2 < (p - q) ^ 2 := by
    have := sq_lt_sq' (by linarith [abs_nonneg (p - q)] : -|p - q| < δ) hδ
    rwa [sq_abs] at this
  have hbc : a * b + a' * b' = 1 - ((a - b) ^ 2 + (a' - b') ^ 2) / 2 := by
    nlinarith [ha2, hb2, ha'2, hb'2]
  nlinarith [sq_nonneg (a' - b')]

/-! ## The stopped process -/

noncomputable def Zrec (G : ℕ → ℝ) (L : ℕ → ℝ) (stop : ℕ → Prop) : ℕ → ℝ
  | 0 => G 0
  | k + 1 => if stop (k + 1) then Zrec G L stop k * L k else G (k + 1)

lemma Zrec_eq_G (G L : ℕ → ℝ) (stop : ℕ → Prop) (k : ℕ) (hk : ¬ stop k) :
    Zrec G L stop k = G k := by
  cases k with
  | zero => rfl
  | succ k => simp only [Zrec, if_neg hk]

lemma Zrec_after (G L : ℕ → ℝ) (stop : ℕ → Prop) (τ : ℕ) (hτ : ¬ stop τ)
    (hafter : ∀ j, τ < j → stop j) :
    ∀ k, τ ≤ k → Zrec G L stop k = G τ * ∏ j ∈ Finset.Ico τ k, L j := by
  intro k hk
  induction k with
  | zero =>
    have : τ = 0 := by omega
    subst this; simp [Zrec]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hk with h | h
    · rw [← h]; simp [Zrec_eq_G G L stop τ hτ]
    · have hk' : τ ≤ k := by omega
      simp only [Zrec, if_pos (hafter (k + 1) h)]
      rw [ih hk', Finset.prod_Ico_succ_top hk', mul_assoc]

lemma Zrec_nonneg (G L : ℕ → ℝ) (stop : ℕ → Prop) (hG : ∀ j, 0 ≤ G j) (hL : ∀ j, 0 ≤ L j) :
    ∀ k, 0 ≤ Zrec G L stop k := by
  intro k
  induction k with
  | zero => exact hG 0
  | succ k ih =>
    simp only [Zrec]
    split_ifs
    · exact mul_nonneg ih (hL k)
    · exact hG _

lemma Zrec_congr (G G' L L' : ℕ → ℝ) (stop stop' : ℕ → Prop) (k : ℕ)
    (hG : ∀ j ≤ k, G j = G' j) (hL : ∀ j < k, L j = L' j) (hs : ∀ j ≤ k, (stop j ↔ stop' j)) :
    Zrec G L stop k = Zrec G' L' stop' k := by
  induction k with
  | zero => simp [Zrec, hG 0 le_rfl]
  | succ k ih =>
    have ih' := ih (fun j hj => hG j (by omega)) (fun j hj => hL j (by omega))
      (fun j hj => hs j (by omega))
    simp only [Zrec]
    by_cases h : stop (k + 1)
    · rw [if_pos h, if_pos ((hs (k+1) le_rfl).mp h), ih', hL k (by omega)]
    · rw [if_neg h, if_neg (fun h' => h ((hs (k+1) le_rfl).mpr h')), hG (k+1) le_rfl]

end CPSolL3

namespace CPSolL3

open scoped Classical

lemma LL_nonneg' (M : Market) (hM : M.Standing) {n T : ℕ} (μ0 : ℝ) (sig : Signal n)
    (α : Promo n T) (π : Pricing n T) (hα : α.IsValid) (hπ : IsMyopic M μ0 sig α π)
    (b : Bool) (s : Fin n) (y : Fin T → Bool) (k : Fin T) : 0 ≤ LL M α π b s k y := by
  have hin := histAt_inPrice M μ0 sig α π hπ s y k (by omega)
  have hp : priceAt π s y k ∈ M.price := by
    simp only [priceAt, Pricing.at, k.isLt, dif_pos]
    exact (hπ k _ hin).1
  have ha : promoAt α π b s y k ∈ Set.Icc (0:ℝ) 1 := by
    simp only [promoAt, Promo.at, k.isLt, dif_pos]; exact hα _ _ _ _
  exact likelihood_nonneg M hM b _ _ ha hp _

lemma PP_nonneg' (M : Market) (hM : M.Standing) {n T : ℕ} (μ0 : ℝ) (sig : Signal n)
    (α : Promo n T) (π : Pricing n T) (hα : α.IsValid) (hπ : IsMyopic M μ0 sig α π)
    (b : Bool) (s : Fin n) (y : Fin T → Bool) (k : ℕ) : 0 ≤ PP M α π b s k y := by
  unfold PP
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact LL_nonneg' M hM μ0 sig α π hα hπ b s y i
  · exact zero_le_one

lemma belief_rel (M : Market) (hM : M.Standing) {n T : ℕ} (μ0 : ℝ)
    (hμ0 : μ0 ∈ Set.Icc (0:ℝ) 1) (sig : Signal n) (hsig : sig.IsValid)
    (α : Promo n T) (π : Pricing n T) (hα : α.IsValid) (hπ : IsMyopic M μ0 sig α π)
    (s : Fin n) (y : Fin T → Bool) : ∀ k : ℕ, k ≤ T →
      belief M μ0 sig α k (histAt π s y k) *
        (μ0 * sig true s * PP M α π true s k y + (1 - μ0) * sig false s * PP M α π false s k y) =
        μ0 * sig true s * PP M α π true s k y := by
  obtain ⟨hμa, hμb⟩ := hμ0
  have hLL := LL_nonneg' M hM μ0 sig α π hα hπ
  have hPP := PP_nonneg' M hM μ0 sig α π hα hπ
  intro k
  induction k with
  | zero =>
    intro _
    simp only [PP_zero, mul_one, belief, histAt]
    have := bayes_rel μ0 μ0 1 (sig true s) (sig false s) hμa (by linarith) (hsig.1 _ _)
      (hsig.1 _ _) (by ring)
    linear_combination this
  | succ k ih =>
    intro hk
    have hkT : k < T := by omega
    have hih := ih (by omega)
    set kk : Fin T := ⟨k, hkT⟩
    have e1 := PP_succ M α π true s kk y
    have e2 := PP_succ M α π false s kk y
    simp only [kk] at e1 e2
    rw [e1, e2]
    rw [belief, histAt_succ_init, histAt_succ_last]
    have hl : ∀ b : Bool, likelihood M b (α.at k (π.at k (histAt π s y k)) b (histAt π s y k))
        (π.at k (histAt π s y k)) (yAt y k) = LL M α π b s kk y := by
      intro b
      simp only [LL, promoAt, priceAt, yAt, hkT, dif_pos, kk]
    rw [hl true, hl false]
    have hN : 0 ≤ μ0 * sig true s * PP M α π true s k y :=
      mul_nonneg (mul_nonneg hμa (hsig.1 _ _)) (hPP _ _ _ _)
    have hDN : 0 ≤ (1 - μ0) * sig false s * PP M α π false s k y :=
      mul_nonneg (mul_nonneg (by linarith) (hsig.1 _ _)) (hPP _ _ _ _)
    have := bayes_rel (belief M μ0 sig α k (histAt π s y k))
      (μ0 * sig true s * PP M α π true s k y)
      (μ0 * sig true s * PP M α π true s k y + (1 - μ0) * sig false s * PP M α π false s k y)
      (LL M α π true s kk y) (LL M α π false s kk y) hN (by linarith) (hLL _ _ _ _)
      (hLL _ _ _ _) hih
    linear_combination this

lemma g_bound (μ WT WF : ℝ) (hT : 0 ≤ WT) (hF : 0 ≤ WF) (hμ : μ ∈ Set.Icc (0:ℝ) 1)
    (hrel : μ * (WT + WF) = WT) :
    μ * WF ≤ √(WT * WF) ∧ (1 - μ) * WT ≤ √(WT * WF) := by
  obtain ⟨h0, h1⟩ := hμ
  set r := √(WT * WF) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = WT * WF := Real.sq_sqrt (mul_nonneg hT hF)
  have hrD : r ≤ WT + WF := by
    have := sqrt_mul_le_add WT WF hT hF; linarith
  rcases eq_or_lt_of_le (add_nonneg hT hF) with hD | hD
  · have hT0 : WT = 0 := by linarith
    have hF0 : WF = 0 := by linarith
    subst hT0; subst hF0; simp; exact hr0
  · constructor
    · -- μ WF (WT+WF) = WT WF = r²
      have : μ * WF * (WT + WF) = r ^ 2 := by rw [hr2]; linear_combination WF * hrel
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_right hc hD
      nlinarith
    · have : (1 - μ) * WT * (WT + WF) = r ^ 2 := by
        rw [hr2]; linear_combination (-WT) * hrel
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_right hc hD
      nlinarith

lemma PP_Ico (M : Market) {n T : ℕ} (α : Promo n T) (π : Pricing n T) (b : Bool) (s : Fin n)
    (y : Fin T → Bool) (τ : ℕ) :
    ∀ k, τ ≤ k → k ≤ T → PP M α π b s k y = PP M α π b s τ y *
      ∏ j ∈ Finset.Ico τ k, (if hj : j < T then LL M α π b s ⟨j, hj⟩ y else 1) := by
  intro k
  induction k with
  | zero => intro h _; have : τ = 0 := by omega
            subst this; simp
  | succ k ih =>
    intro h1 h2
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · rw [← h]; simp
    · have hkT : k < T := by omega
      rw [Finset.prod_Ico_succ_top (by omega), ← mul_assoc, ← ih (by omega) (by omega),
        dif_pos hkT]
      exact PP_succ M α π b s ⟨k, hkT⟩ y

end CPSolL3

namespace CPSolL3
open scoped Classical

lemma reach_min {T : ℕ} (P : Fin T → Prop) (m : ℕ) (hm1 : 1 ≤ m) (h : (reach P m).Nonempty) :
    P ((reach P m).min' h) ∧ cnt P ((reach P m).min' h) = m := by
  set ts := (reach P m).min' h with hts
  have hts_mem : m ≤ cnt P ts := by
    have := Finset.min'_mem (reach P m) h
    rw [← hts] at this
    simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  set A := univ.filter (fun t' : Fin T => t' < ts ∧ P t') with hA
  have hAc : A.card < m := by
    by_cases hAe : A.Nonempty
    · set t'' := A.max' hAe
      have ht''A := Finset.max'_mem A hAe
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at ht''A
      have hcnt : cnt P t'' = A.card := by
        unfold cnt
        congr 1
        ext t'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA]
        constructor
        · intro h'; exact ⟨lt_of_le_of_lt h'.1 ht''A.1, h'.2⟩
        · intro h'; exact ⟨Finset.le_max' _ _ (by simp [hA, h']), h'.2⟩
      have hnot : t'' ∉ reach P m := by
        intro hmem
        have := Finset.min'_le _ _ hmem
        rw [← hts] at this
        exact absurd ht''A.1 (not_lt.mpr this)
      simp only [reach, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hAe
      rw [hAe, Finset.card_empty]; omega
  by_cases hP : P ts
  · have hc : cnt P ts = A.card + 1 := by
      unfold cnt
      have : univ.filter (fun t' : Fin T => t' ≤ ts ∧ P t') = insert ts A := by
        ext t'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, hA]
        constructor
        · intro h'
          rcases eq_or_lt_of_le h'.1 with he | hl
          · left; exact he
          · right; exact ⟨hl, h'.2⟩
        · rintro (he | h')
          · rw [he]; exact ⟨le_refl _, hP⟩
          · exact ⟨h'.1.le, h'.2⟩
      rw [this, Finset.card_insert_of_notMem]
      simp [hA]
    exact ⟨hP, by omega⟩
  · exfalso
    have hc : cnt P ts = A.card := by
      unfold cnt
      congr 1
      ext t'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hA]
      constructor
      · intro h'
        rcases eq_or_lt_of_le h'.1 with he | hl
        · exact absurd (he ▸ h'.2) hP
        · exact ⟨hl, h'.2⟩
      · intro h'; exact ⟨h'.1.le, h'.2⟩
    omega

end CPSolL3

namespace CPSolL3
open scoped Classical

lemma bayes_zero' (a b : ℝ) : bayes 0 a b = 0 := by
  unfold bayes; split_ifs <;> simp

lemma bayes_one' (a b : ℝ) : bayes 1 a b = 1 := by
  unfold bayes; split_ifs with h
  · rfl
  · simp only [one_mul, sub_self, zero_mul, add_zero] at h ⊢
    exact div_self h

lemma belief_zero (M : Market) {n T : ℕ} (sig : Signal n) (α : Promo n T) :
    ∀ t (h : SHist n t), belief M 0 sig α t h = 0 := by
  intro t
  induction t with
  | zero => intro h; simp [belief, bayes_zero']
  | succ t ih => intro h; rw [belief, ih, bayes_zero']

lemma belief_one (M : Market) {n T : ℕ} (sig : Signal n) (α : Promo n T) :
    ∀ t (h : SHist n t), belief M 1 sig α t h = 1 := by
  intro t
  induction t with
  | zero => intro h; simp [belief, bayes_one']
  | succ t ih => intro h; rw [belief, ih, bayes_one']

lemma WC_eq_Wmax_at (M : Market) (μ : ℝ) (hμ : μ = 0 ∨ μ = 1) : WC M μ = Wmax M μ := by
  unfold WC Wmax
  congr 1
  ext v
  constructor
  · rintro ⟨a, p, ha, hm, _, rfl⟩; exact ⟨a, p, ha, hm, rfl⟩
  · rintro ⟨a, p, ha, hm, rfl⟩
    refine ⟨a, p, ha, hm, ?_, rfl⟩
    intro y
    rcases hμ with h | h <;> subst h
    · exact bayes_zero' _ _
    · exact bayes_one' _ _

lemma no_excess (M : Market) (hM : M.Standing) {n T : ℕ} (ε : ℝ) (hε : 0 < ε) (μ0 : ℝ)
    (hμ0 : μ0 = 0 ∨ μ0 = 1) (sig : Signal n) (α : Promo n T) (π : Pricing n T)
    (hα : α.IsValid) (hπ : IsMyopic M μ0 sig α π) (t : Fin T) (h : SHist n t)
    (hh : h.InPrice M) : ¬ InExcess M ε μ0 sig α π t h := by
  intro hex
  unfold InExcess periodSurplus at hex
  have hb : belief M μ0 sig α t h = μ0 := by
    rcases hμ0 with h0 | h0 <;> subst h0
    · exact belief_zero M sig α t h
    · exact belief_one M sig α t h
  rw [hb] at hex
  have hmem : μ0 ∈ Set.Icc (0:ℝ) 1 := by
    rcases hμ0 with h0 | h0 <;> subst h0 <;> norm_num
  have hmy := hπ t h hh
  rw [hb] at hmy
  have hW : expSurplus M μ0 (fun q b => α t q b h) (π t h) ≤ Wmax M μ0 :=
    le_csSup (Wmax_bdd M hM μ0 hmem) ⟨_, _, fun q b => hα t q b h, hmy, rfl⟩
  have hco := le_co (WC M) _ (fun x hx => WC_le M hM x hx) μ0 hmem
  rw [WC_eq_Wmax_at M μ0 hμ0] at hco
  linarith

end CPSolL3

open CPSolL3

set_option maxHeartbeats 1000000 in
theorem solution (M : Market) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε)
    (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0 : ℝ) 1) :
    ∃ χ β : ℝ, 0 < χ ∧ 0 < β ∧
      ∀ (T n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T),
        sig.IsValid → α.IsValid → IsSinglePrice M α → IsBeliefBased M μ0 sig α →
        IsMyopic M μ0 sig α π →
        ∀ m : ℕ, 1 ≤ m →
          condExpect M sig α π false (fun s y => hitBelief M ε μ0 sig α π false s y m)
              ≤ χ * Real.exp (-β * m) ∧
          condExpect M sig α π true (fun s y => 1 - hitBelief M ε μ0 sig α π true s y m)
              ≤ χ * Real.exp (-β * m) := by
  classical
  obtain ⟨δ, hδ, h2⟩ := lemma_2 M hM ε hε
  set δ' := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  set c := 1 - δ' ^ 2 / 8 with hc
  have hc0 : 0 < c := by nlinarith
  have hc1 : c < 1 := by nlinarith
  set β := -Real.log c with hβ
  have hβ0 : 0 < β := by rw [hβ]; have := Real.log_neg hc0 hc1; linarith
  have hexp : ∀ m : ℕ, Real.exp (-β * m) = c ^ m := by
    intro m; rw [hβ, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hc0]
  obtain ⟨hμa, hμb⟩ := hμ0
  set K0 := √(μ0 / (1 - μ0)) + √((1 - μ0) / μ0) with hK0
  have hK00 : 0 ≤ K0 := by positivity
  refine ⟨(K0 + 1) / c, β, by positivity, hβ0, ?_⟩
  intro T n sig α π hsig hα hsp hbb hπ m hm
  rw [hexp m]
  have hχc : (K0 + 1) / c * c ^ m = (K0 + 1) * c ^ (m - 1) := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [hχc]
  have hcm : 0 ≤ c ^ (m - 1) := pow_nonneg hc0.le _
  -- basic objects
  set P : Fin n → (Fin T → Bool) → Fin T → Prop :=
    fun s y t => InExcess M ε μ0 sig α π t (histAt π s y t) with hPdef
  set e : Fin n → (Fin T → Bool) → ℕ → Prop :=
    fun s y j => ∃ hj : j < T, P s y ⟨j, hj⟩ with hedef
  set N : Fin n → (Fin T → Bool) → ℕ → ℕ :=
    fun s y j => ((Finset.range j).filter (fun i => e s y i)).card with hNdef
  set W : Bool → Fin n → (Fin T → Bool) → ℕ → ℝ :=
    fun b s y k => prior μ0 b * sig b s * PP M α π b s k y with hWdef
  set G : Fin n → (Fin T → Bool) → ℕ → ℝ :=
    fun s y k => √(W true s y k * W false s y k) * (1 / c) ^ (N s y k) with hGdef
  set Lb : Bool → Fin n → (Fin T → Bool) → ℕ → ℝ :=
    fun b s y j => if hj : j < T then LL M α π b s ⟨j, hj⟩ y else 1 with hLbdef
  set stop : Fin n → (Fin T → Bool) → ℕ → Prop := fun s y j => m ≤ N s y j with hstopdef
  set Z : Bool → Fin n → (Fin T → Bool) → ℕ → ℝ :=
    fun b s y k => Zrec (G s y) (Lb b s y) (stop s y) k with hZdef
  set g : Bool → ℝ → ℝ := fun b x => if b then 1 - x else x with hgdef
  have hprior0 : ∀ b, 0 ≤ prior μ0 b := by
    intro b; unfold prior; split_ifs <;> linarith
  have hPP := PP_nonneg' M hM μ0 sig α π hα hπ
  have hLL := LL_nonneg' M hM μ0 sig α π hα hπ
  have hW0 : ∀ b s y k, 0 ≤ W b s y k := fun b s y k =>
    mul_nonneg (mul_nonneg (hprior0 b) (hsig.1 _ _)) (hPP _ _ _ _)
  have hG0 : ∀ s y k, 0 ≤ G s y k := fun s y k =>
    mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (by positivity) _)
  have hLb0 : ∀ b s y j, 0 ≤ Lb b s y j := by
    intro b s y j; simp only [hLbdef]; split_ifs
    · exact hLL _ _ _ _
    · exact zero_le_one
  have hZ0 : ∀ b s y k, 0 ≤ Z b s y k := fun b s y k =>
    Zrec_nonneg _ _ _ (hG0 s y) (hLb0 b s y) k
  -- dependencies
  have he_dep : ∀ s y y' (i : ℕ), (∀ t : Fin T, (t : ℕ) < i → y t = y' t) →
      (e s y i ↔ e s y' i) := by
    intro s y y' i h
    simp only [hedef, hPdef]
    rw [histAt_dep π s y y' i h]
  have hN_dep : ∀ s y y' (j : ℕ), (∀ t : Fin T, (t : ℕ) + 1 < j → y t = y' t) →
      N s y j = N s y' j := by
    intro s y y' j h
    simp only [hNdef]
    congr 1
    apply Finset.filter_congr
    intro i hi
    rw [Finset.mem_range] at hi
    exact he_dep s y y' i (fun t ht => h t (by omega))
  have hN_mono : ∀ s y j, N s y j ≤ N s y (j + 1) := by
    intro s y j
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    exact ⟨by omega, hi.2⟩
  have hN_mono' : ∀ s y j k, j ≤ k → N s y j ≤ N s y k := by
    intro s y j k hjk
    induction k with
    | zero => have : j = 0 := by omega
              subst this; exact le_rfl
    | succ k ih =>
      rcases Nat.eq_or_lt_of_le hjk with h | h
      · rw [h]
      · exact le_trans (ih (by omega)) (hN_mono s y k)
  have hN_succ : ∀ s y j, N s y (j + 1) = N s y j + (if e s y j then 1 else 0) := by
    intro s y j
    simp only [hNdef, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem]
      simp
    · simp
  have hW_dep : ∀ b s y y' (k : ℕ), (∀ t : Fin T, (t : ℕ) < k → y t = y' t) →
      W b s y k = W b s y' k := by
    intro b s y y' k h
    simp only [hWdef]
    rw [PP_dep M α π b s k y y' h]
  have hG_dep : ∀ s y y' (k : ℕ), (∀ t : Fin T, (t : ℕ) < k → y t = y' t) →
      G s y k = G s y' k := by
    intro s y y' k h
    simp only [hGdef]
    rw [hW_dep true s y y' k h, hW_dep false s y y' k h,
      hN_dep s y y' k (fun t ht => h t (by omega))]
  have hLb_dep : ∀ b s y y' (j : ℕ), (∀ t : Fin T, (t : ℕ) < j + 1 → y t = y' t) →
      Lb b s y j = Lb b s y' j := by
    intro b s y y' j h
    simp only [hLbdef]
    split_ifs with hj
    · exact LL_dep M α π b s ⟨j, hj⟩ y y' h
    · rfl
  have hZ_dep : ∀ b s y y' (k : ℕ), (∀ t : Fin T, (t : ℕ) < k → y t = y' t) →
      Z b s y k = Z b s y' k := by
    intro b s y y' k h
    simp only [hZdef]
    apply Zrec_congr
    · intro j hj; exact hG_dep s y y' j (fun t ht => h t (by omega))
    · intro j hj; exact hLb_dep b s y y' j (fun t ht => h t (by omega))
    · intro j hj
      simp only [hstopdef]
      rw [hN_dep s y y' j (fun t ht => h t (by omega))]
  -- separation at excess periods
  have hsep : ∀ s y (k : ℕ) (hk : k < T), e s y k →
      δ' < |saleProb M true (promoAt α π true s y k) (priceAt π s y k) -
        saleProb M false (promoAt α π false s y k) (priceAt π s y k)| := by
    intro s y k hk hek
    obtain ⟨hk', hP⟩ := hek
    set kk : Fin T := ⟨k, hk⟩
    set h := histAt π s y k
    have hin : h.InPrice M := histAt_inPrice M μ0 sig α π hπ s y k hk.le
    have hmem := belief_mem M hM μ0 ⟨hμa, hμb⟩ sig hsig α hα k h hin
    obtain ⟨pbar, hpbar, hsing⟩ := hsp kk h hin
    have hmy := hπ kk h hin
    have hP' : co (WC M) (belief M μ0 sig α kk h) + ε <
        expSurplus M (belief M μ0 sig α kk h) (fun q b => α kk q b h) (π kk h) := hP
    have := h2 _ hmem (fun q b => α kk q b h) (π kk h) (fun q b => hα kk q b h)
      ⟨pbar, hpbar, fun q hq hne b => hsing q hq hne b⟩ hmy hP'
    have hpr : priceAt π s y k = π kk h := by
      simp [priceAt, Pricing.at, hk, kk, h]
    have hpro : ∀ b, promoAt α π b s y k = α kk (π kk h) b h := by
      intro b; simp [promoAt, Promo.at, hk, hpr, kk, h]
    rw [hpro true, hpro false, hpr]
    exact lt_of_le_of_lt hδ'δ this
  -- supermartingale step
  have hstep : ∀ b s (k : ℕ), k < T → ∑ y, Z b s y (k + 1) ≤ (1 / 2) * ∑ y, Z b s y k := by
    intro b s k hk
    set kk : Fin T := ⟨k, hk⟩
    have hpair : ∀ y, Z b s y (k + 1) + Z b s (flipAt kk y) (k + 1) ≤ Z b s y k := by
      intro y
      set y' := flipAt kk y with hy'
      have hag : ∀ t : Fin T, (t : ℕ) < k → y t = y' t :=
        fun t ht => (flipAt_agree kk y t ht).symm
      have hZk : Z b s y' k = Z b s y k := (hZ_dep b s y y' k hag).symm
      have hNk1 : N s y (k + 1) = N s y' (k + 1) := hN_dep s y y' (k + 1) (fun t ht => hag t (by omega))
      by_cases hst : stop s y (k + 1)
      · have hst' : stop s y' (k + 1) := by simp only [hstopdef] at hst ⊢; rw [← hNk1]; exact hst
        have e1 : Z b s y (k + 1) = Z b s y k * Lb b s y k := by
          simp only [hZdef, Zrec, if_pos hst]
        have e2 : Z b s y' (k + 1) = Z b s y' k * Lb b s y' k := by
          simp only [hZdef, Zrec, if_pos hst']
        rw [e1, e2, hZk]
        have hsum : Lb b s y k + Lb b s y' k = 1 := by
          simp only [hLbdef, dif_pos hk]
          exact LL_flip_add M α π b s kk y
        have := hZ0 b s y k
        nlinarith
      · have hst' : ¬ stop s y' (k + 1) := by
          simp only [hstopdef] at hst ⊢; rw [← hNk1]; exact hst
        have hstk : ¬ stop s y k := by
          simp only [hstopdef] at hst ⊢
          have := hN_mono s y k; omega
        have e0 : Z b s y k = G s y k := Zrec_eq_G _ _ _ k hstk
        have e1 : Z b s y (k + 1) = G s y (k + 1) := by
          simp only [hZdef, Zrec, if_neg hst]
        have e2 : Z b s y' (k + 1) = G s y' (k + 1) := by
          simp only [hZdef, Zrec, if_neg hst']
        rw [e0, e1, e2]
        -- expand G (k+1)
        have hWs : ∀ (bb : Bool) (z : Fin T → Bool), W bb s z (k + 1) = W bb s z k * LL M α π bb s kk z := by
          intro bb z
          simp only [hWdef]
          rw [PP_succ M α π bb s kk z]
          ring
        have hGs : ∀ z : Fin T → Bool, G s z (k + 1) =
            √(W true s z k * W false s z k) * (1 / c) ^ (N s z k) *
              (√(LL M α π true s kk z * LL M α π false s kk z) *
                (1 / c) ^ (if e s z k then 1 else 0)) := by
          intro z
          simp only [hGdef]
          rw [hWs true z, hWs false z, hN_succ s z k, pow_add]
          have : W true s z k * LL M α π true s kk z * (W false s z k * LL M α π false s kk z) =
              (W true s z k * W false s z k) * (LL M α π true s kk z * LL M α π false s kk z) := by
            ring
          rw [this, Real.sqrt_mul (mul_nonneg (hW0 _ _ _ _) (hW0 _ _ _ _))]
          ring
        rw [hGs y, hGs y']
        have hWy' : ∀ bb, W bb s y' k = W bb s y k := fun bb => (hW_dep bb s y y' k hag).symm
        have hNy' : N s y' k = N s y k := (hN_dep s y y' k (fun t ht => hag t (by omega))).symm
        have hey' : (e s y' k ↔ e s y k) := (he_dep s y y' k hag).symm
        rw [hWy' true, hWy' false, hNy']
        have hGk : G s y k = √(W true s y k * W false s y k) * (1 / c) ^ (N s y k) := rfl
        rw [hGk]
        set A := √(W true s y k * W false s y k) * (1 / c) ^ (N s y k) with hA
        have hA0 : 0 ≤ A := hG0 s y k
        -- the Bhattacharyya sum
        have hhist : histAt π s y' k = histAt π s y k := (histAt_dep π s y y' k hag).symm
        have hkk : ((kk : Fin T) : ℕ) = k := rfl
        set pT := saleProb M true (promoAt α π true s y k) (priceAt π s y k) with hpT
        set pF := saleProb M false (promoAt α π false s y k) (priceAt π s y k) with hpF
        have hpT' : saleProb M true (promoAt α π true s y' k) (priceAt π s y' k) = pT := by
          simp only [hpT, promoAt, priceAt, hhist]
        have hpF' : saleProb M false (promoAt α π false s y' k) (priceAt π s y' k) = pF := by
          simp only [hpF, promoAt, priceAt, hhist]
        have hin : (histAt π s y k).InPrice M := histAt_inPrice M μ0 sig α π hπ s y k hk.le
        have hprice : priceAt π s y k ∈ M.price := by
          simp only [priceAt, Pricing.at, dif_pos hk]; exact (hπ kk _ hin).1
        have hpromo : ∀ bb, promoAt α π bb s y k ∈ Set.Icc (0:ℝ) 1 := by
          intro bb; simp only [promoAt, Promo.at, dif_pos hk]; exact hα _ _ _ _
        have hpTm : pT ∈ Set.Icc (0:ℝ) 1 := saleProb_mem M hM true _ _ (hpromo true) hprice
        have hpFm : pF ∈ Set.Icc (0:ℝ) 1 := saleProb_mem M hM false _ _ (hpromo false) hprice
        have hyk : y' kk = !(y kk) := by simp [hy', flipAt]
        have hBC : √(LL M α π true s kk y * LL M α π false s kk y) +
            √(LL M α π true s kk y' * LL M α π false s kk y') =
            √(pT * pF) + √((1 - pT) * (1 - pF)) := by
          simp only [LL, hkk]
          rw [hyk]
          simp only [likelihood]
          rw [hpT', hpF']
          cases y kk <;> simp <;> ring
        by_cases hek : e s y k
        · have hek' : e s y' k := hey'.mpr hek
          rw [if_pos hek, if_pos hek']
          have hsepk := hsep s y k hk hek
          have hbc := bc_le pT pF δ' hpTm hpFm hδ'0.le hsepk
          have h1c : (1 / c) ^ 1 * c = 1 := by field_simp
          have : A * (√(LL M α π true s kk y * LL M α π false s kk y) * (1 / c) ^ 1) +
              A * (√(LL M α π true s kk y' * LL M α π false s kk y') * (1 / c) ^ 1) =
              A * (1 / c) ^ 1 * (√(pT * pF) + √((1 - pT) * (1 - pF))) := by
            rw [← hBC]; ring
          rw [this]
          have hle : A * (1 / c) ^ 1 * (√(pT * pF) + √((1 - pT) * (1 - pF))) ≤
              A * (1 / c) ^ 1 * c := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA0 (by positivity))
            rw [hc]; exact hbc
          have hAc : A * (1 / c) ^ 1 * c = A := by field_simp
          linarith
        · have hek' : ¬ e s y' k := fun h => hek (hey'.mp h)
          rw [if_neg hek, if_neg hek']
          have hbc := bc_le_one pT pF hpTm hpFm
          have : A * (√(LL M α π true s kk y * LL M α π false s kk y) * (1 / c) ^ 0) +
              A * (√(LL M α π true s kk y' * LL M α π false s kk y') * (1 / c) ^ 0) =
              A * (√(pT * pF) + √((1 - pT) * (1 - pF))) := by
            rw [← hBC]; ring
          rw [this]
          nlinarith
    have hflip : ∑ y, Z b s (flipAt kk y) (k + 1) = ∑ y, Z b s y (k + 1) :=
      sum_flip kk (fun y => Z b s y (k + 1))
    have := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hpair y)
    rw [Finset.sum_add_distrib, hflip] at this
    linarith
  -- iterate the supermartingale inequality
  have hiter : ∀ b s (k : ℕ), k ≤ T → ∑ y, Z b s y k ≤ (1 / 2) ^ k * ∑ y, Z b s y 0 := by
    intro b s k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := hstep b s k (by omega)
      have h2 := ih (by omega)
      rw [pow_succ]
      nlinarith
  set G0 : Fin n → ℝ := fun s => √((μ0 * sig true s) * ((1 - μ0) * sig false s)) with hG0def
  have hZ0val : ∀ b s y, Z b s y 0 = G0 s := by
    intro b s y
    simp [hZdef, Zrec, hGdef, hWdef, hNdef, PP_zero, prior, hG0def]
  have hsumZT : ∀ b s, ∑ y, Z b s y T ≤ G0 s := by
    intro b s
    have h := hiter b s T le_rfl
    simp only [hZ0val, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h
    have : (1 / 2 : ℝ) ^ T * (2 ^ T * G0 s) = G0 s := by
      rw [← mul_assoc, ← mul_pow]; norm_num
    linarith
  -- counting identity
  have hNcnt : ∀ s y (j : Fin T), N s y ((j : ℕ) + 1) = cnt (P s y) j := by
    intro s y j
    simp only [hNdef, cnt]
    have : (Finset.range ((j : ℕ) + 1)).filter (fun i => e s y i) =
        (univ.filter (fun t : Fin T => t ≤ j ∧ P s y t)).map Fin.valEmbedding := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, hedef]
      constructor
      · rintro ⟨hi, hiT, hP⟩
        exact ⟨⟨i, hiT⟩, ⟨Fin.mk_le_of_le_val (by omega), hP⟩, rfl⟩
      · rintro ⟨t, ⟨htj, hP⟩, rfl⟩
        exact ⟨by have := Fin.le_iff_val_le_val.mp htj; omega, t.isLt, hP⟩
    rw [this, Finset.card_map]
  -- pointwise bound
  have hpt : ∀ b s y, W b s y T * g b (hitBelief M ε μ0 sig α π b s y m) ≤
      c ^ (m - 1) * Z b s y T := by
    intro b s y
    unfold hitBelief
    have hrs : reachSet M ε μ0 sig α π s y m = reach (P s y) m := rfl
    by_cases hne : (reach (P s y) m).Nonempty
    · have hne' : (reachSet M ε μ0 sig α π s y m).Nonempty := hrs ▸ hne
      rw [dif_pos hne']
      have hτeq : (reachSet M ε μ0 sig α π s y m).min' hne' = (reach (P s y) m).min' hne := rfl
      obtain ⟨hPτ, hcntτ⟩ := reach_min (P s y) m hm hne
      rw [hτeq]
      set τf := (reach (P s y) m).min' hne with hτf
      set τ : ℕ := (τf : ℕ) with hτ
      have hτT : τ < T := τf.isLt
      have hNτ1 : N s y (τ + 1) = m := by rw [hNcnt s y τf, hcntτ]
      have heτ : e s y τ := ⟨hτT, hPτ⟩
      have hNτ : N s y τ = m - 1 := by
        have := hN_succ s y τ
        rw [if_pos heτ, hNτ1] at this
        omega
      have hnstop : ¬ stop s y τ := by
        simp only [hstopdef]; omega
      have hafter : ∀ j, τ < j → stop s y j := by
        intro j hj
        simp only [hstopdef]
        have := hN_mono' s y (τ + 1) j (by omega)
        omega
      have hZT : Z b s y T = G s y τ * ∏ j ∈ Finset.Ico τ T, Lb b s y j :=
        Zrec_after (G s y) (Lb b s y) (stop s y) τ hnstop hafter T hτT.le
      have hWT : W b s y T = W b s y τ * ∏ j ∈ Finset.Ico τ T, Lb b s y j := by
        simp only [hWdef, hLbdef]
        rw [PP_Ico M α π b s y τ T hτT.le le_rfl]
        ring
      have hin : (histAt π s y τ).InPrice M := histAt_inPrice M μ0 sig α π hπ s y τ hτT.le
      have hbm := belief_mem M hM μ0 ⟨hμa, hμb⟩ sig hsig α hα τ _ hin
      have hrel := belief_rel M hM μ0 ⟨hμa, hμb⟩ sig hsig α π hα hπ s y τ hτT.le
      have hrel' : belief M μ0 sig α τ (histAt π s y τ) * (W true s y τ + W false s y τ) =
          W true s y τ := by
        simp only [hWdef, prior, if_true, Bool.false_eq_true, if_false]
        exact hrel
      obtain ⟨gF, gT⟩ := g_bound _ _ _ (hW0 true s y τ) (hW0 false s y τ) hbm hrel'
      have hcc : (1 / c) ^ (m - 1) * c ^ (m - 1) = 1 := by
        rw [← mul_pow, one_div, inv_mul_cancel₀ hc0.ne', one_pow]
      have hGτ : √(W true s y τ * W false s y τ) = G s y τ * c ^ (m - 1) := by
        have hG' : G s y τ = √(W true s y τ * W false s y τ) * (1 / c) ^ (m - 1) := by
          rw [← hNτ]
        rw [hG']
        set X := √(W true s y τ * W false s y τ)
        rw [show X * (1 / c) ^ (m - 1) * c ^ (m - 1) = X * ((1 / c) ^ (m - 1) * c ^ (m - 1)) by ring,
          hcc, mul_one]
      have hProd : 0 ≤ ∏ j ∈ Finset.Ico τ T, Lb b s y j :=
        Finset.prod_nonneg (fun j _ => hLb0 b s y j)
      rw [hWT, hZT]
      cases b
      · simp only [hgdef, Bool.false_eq_true, if_false]
        rw [hGτ] at gF
        have := mul_le_mul_of_nonneg_right gF hProd
        calc W false s y τ * (∏ j ∈ Finset.Ico τ T, Lb false s y j) *
              belief M μ0 sig α τ (histAt π s y τ)
            = belief M μ0 sig α τ (histAt π s y τ) * W false s y τ *
                (∏ j ∈ Finset.Ico τ T, Lb false s y j) := by ring
          _ ≤ G s y τ * c ^ (m - 1) * (∏ j ∈ Finset.Ico τ T, Lb false s y j) := this
          _ = c ^ (m - 1) * (G s y τ * ∏ j ∈ Finset.Ico τ T, Lb false s y j) := by ring
      · simp only [hgdef, if_true]
        rw [hGτ] at gT
        have := mul_le_mul_of_nonneg_right gT hProd
        calc W true s y τ * (∏ j ∈ Finset.Ico τ T, Lb true s y j) *
              (1 - belief M μ0 sig α τ (histAt π s y τ))
            = (1 - belief M μ0 sig α τ (histAt π s y τ)) * W true s y τ *
                (∏ j ∈ Finset.Ico τ T, Lb true s y j) := by ring
          _ ≤ G s y τ * c ^ (m - 1) * (∏ j ∈ Finset.Ico τ T, Lb true s y j) := this
          _ = c ^ (m - 1) * (G s y τ * ∏ j ∈ Finset.Ico τ T, Lb true s y j) := by ring
    · have hne' : ¬ (reachSet M ε μ0 sig α π s y m).Nonempty := hrs ▸ hne
      rw [dif_neg hne']
      have := mul_nonneg hcm (hZ0 b s y T)
      cases b
      · simp only [hgdef, Bool.false_eq_true, if_false, mul_zero]; exact this
      · simp only [hgdef, if_true, sub_self, mul_zero]; exact this
  -- sum over signals
  have hG0sum : ∑ s, G0 s ≤ √(μ0 * (1 - μ0)) := by
    have : ∀ s, G0 s = √(μ0 * (1 - μ0)) * √(sig true s * sig false s) := by
      intro s
      simp only [hG0def]
      rw [← Real.sqrt_mul (mul_nonneg hμa (by linarith))]
      congr 1; ring
    simp only [this, ← Finset.mul_sum]
    have hs : ∑ s, √(sig true s * sig false s) ≤ 1 := by
      calc ∑ s, √(sig true s * sig false s) ≤ ∑ s, (sig true s + sig false s) / 2 :=
            Finset.sum_le_sum (fun s _ => sqrt_mul_le_add _ _ (hsig.1 _ _) (hsig.1 _ _))
        _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, hsig.2, hsig.2]; norm_num
    have := Real.sqrt_nonneg (μ0 * (1 - μ0))
    nlinarith
  have hmain : ∀ b, prior μ0 b * condExpect M sig α π b
      (fun s y => g b (hitBelief M ε μ0 sig α π b s y m)) ≤ c ^ (m - 1) * √(μ0 * (1 - μ0)) := by
    intro b
    have e1 : prior μ0 b * condExpect M sig α π b
        (fun s y => g b (hitBelief M ε μ0 sig α π b s y m)) =
        ∑ s, ∑ y, W b s y T * g b (hitBelief M ε μ0 sig α π b s y m) := by
      unfold condExpect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro s _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro y _
      simp only [hWdef, PP_T]
      ring
    rw [e1]
    calc ∑ s, ∑ y, W b s y T * g b (hitBelief M ε μ0 sig α π b s y m)
        ≤ ∑ s, ∑ y, c ^ (m - 1) * Z b s y T :=
          Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun y _ => hpt b s y))
      _ = c ^ (m - 1) * ∑ s, ∑ y, Z b s y T := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; rw [Finset.mul_sum]
      _ ≤ c ^ (m - 1) * ∑ s, G0 s :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => hsumZT b s)) hcm
      _ ≤ c ^ (m - 1) * √(μ0 * (1 - μ0)) := mul_le_mul_of_nonneg_left hG0sum hcm
  -- the degenerate priors
  have hdeg : (μ0 = 0 ∨ μ0 = 1) → ∀ s y, ¬ (reachSet M ε μ0 sig α π s y m).Nonempty := by
    intro h01 s y
    rintro ⟨t, ht⟩
    have ht' : m ≤ excessCount M ε μ0 sig α π s y t := by
      unfold reachSet at ht; exact (Finset.mem_filter.mp ht).2
    unfold excessCount at ht'
    have hz : (univ.filter (fun t' : Fin T => t' ≤ t ∧
        InExcess M ε μ0 sig α π t' (histAt π s y t'))) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro t' _ h
      exact no_excess M hM ε hε μ0 h01 sig α π hα hπ t' _
        (histAt_inPrice M μ0 sig α π hπ s y t' t'.isLt.le) h.2
    rw [hz, Finset.card_empty] at ht'
    omega
  have hKpos : 0 ≤ (K0 + 1) * c ^ (m - 1) := mul_nonneg (by linarith) hcm
  constructor
  · -- state φ_L
    by_cases h1 : μ0 = 1
    · have : condExpect M sig α π false (fun s y => hitBelief M ε μ0 sig α π false s y m) = 0 := by
        unfold condExpect
        apply Finset.sum_eq_zero; intro s _
        have : ∀ y, hitBelief M ε μ0 sig α π false s y m = 0 := by
          intro y; unfold hitBelief; rw [dif_neg (hdeg (Or.inr h1) s y)]; simp
        simp [this]
      rw [this]; exact hKpos
    · have hpos : 0 < 1 - μ0 := by
        rcases lt_or_eq_of_le hμb with h | h
        · linarith
        · exact absurd h h1
      have hm' := hmain false
      simp only [hgdef, Bool.false_eq_true, if_false, prior] at hm'
      have hsq : √(μ0 * (1 - μ0)) ≤ (1 - μ0) * K0 := by
        have : √(μ0 * (1 - μ0)) = (1 - μ0) * √(μ0 / (1 - μ0)) := by
          rw [show μ0 * (1 - μ0) = (1 - μ0) ^ 2 * (μ0 / (1 - μ0)) by field_simp]
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le]
        rw [this]
        apply mul_le_mul_of_nonneg_left _ hpos.le
        rw [hK0]; have := Real.sqrt_nonneg ((1 - μ0) / μ0); linarith
      have hce : (1 - μ0) * condExpect M sig α π false
          (fun s y => hitBelief M ε μ0 sig α π false s y m) ≤ (1 - μ0) * (K0 * c ^ (m - 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left hsq hcm]
      have := le_of_mul_le_mul_left hce hpos
      nlinarith
  · -- state φ_H
    by_cases h0 : μ0 = 0
    · have : condExpect M sig α π true (fun s y => 1 - hitBelief M ε μ0 sig α π true s y m) = 0 := by
        unfold condExpect
        apply Finset.sum_eq_zero; intro s _
        have : ∀ y, hitBelief M ε μ0 sig α π true s y m = 1 := by
          intro y; unfold hitBelief; rw [dif_neg (hdeg (Or.inl h0) s y)]; simp
        simp [this]
      rw [this]; exact hKpos
    · have hpos : 0 < μ0 := lt_of_le_of_ne hμa (Ne.symm h0)
      have hm' := hmain true
      simp only [hgdef, if_true, prior] at hm'
      have hsq : √(μ0 * (1 - μ0)) ≤ μ0 * K0 := by
        have : √(μ0 * (1 - μ0)) = μ0 * √((1 - μ0) / μ0) := by
          rw [show μ0 * (1 - μ0) = μ0 ^ 2 * ((1 - μ0) / μ0) by field_simp]
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le]
        rw [this]
        apply mul_le_mul_of_nonneg_left _ hpos.le
        rw [hK0]; have := Real.sqrt_nonneg (μ0 / (1 - μ0)); linarith
      have hce : μ0 * condExpect M sig α π true
          (fun s y => 1 - hitBelief M ε μ0 sig α π true s y m) ≤ μ0 * (K0 * c ^ (m - 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left hsq hcm]
      have := le_of_mul_le_mul_left hce hpos
      nlinarith
