-- Prove2me | solution 1 for ConfoundPromo.LongRun.upper_bound_display
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:59:46.503805+00:00
-- url     : https://prove2.me/submissions/55720e0c-6262-4070-babd-0f1e653560a6

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model
import Theorems.Thm_ConfoundPromo_LongRun_lemma_3
import Theorems.Thm_ConfoundPromo_LongRun_lemma_4
import Theorems.Thm_ConfoundPromo_LongRun_step_31_a

open ConfoundPromo.LongRun
open Finset

namespace CPSolUB

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

end CPSolUB

namespace CPSolUB

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

end CPSolUB

namespace CPSolUB

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

end CPSolUB

open CPSolUB

theorem solution (M : Market) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε)
    (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ Tbar : ℕ, ∀ T : ℕ, Tbar < T →
      ∀ (n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T),
        sig.IsValid → α.IsValid → IsSinglePrice M α → IsBeliefBased M μ sig α →
        IsMyopic M μ sig α π →
        surplusT M μ sig α π / T < co (WC M) μ + 5 / 4 * ε := by
  classical
  obtain ⟨Cbar, hC0, hC⟩ := lemma_4 M hM ε hε
  obtain ⟨χ, β, hχ, hβ, h3⟩ := lemma_3 M hM (ε / 2) (by linarith) μ hμ
  set r := Real.exp (-β) with hr
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set K := Cbar * χ * (r / (1 - r)) with hKdef
  have hK : 0 ≤ K := by
    apply mul_nonneg (mul_nonneg hC0 hχ.le)
    exact div_nonneg hr0.le (by linarith)
  refine ⟨⌈4 * K / ε⌉₊, ?_⟩
  intro T hT n sig α π hsig hα hsp hbb hπ
  have hTr : 4 * K / ε < T := Nat.lt_of_ceil_lt hT
  have hTpos : (0:ℝ) < T := by
    have : 0 < T := lt_of_le_of_lt (Nat.zero_le _) hT
    exact_mod_cast this
  have hKT : 4 * K < T * ε := (div_lt_iff₀ hε).mp hTr
  obtain ⟨hμa, hμb⟩ := hμ
  -- nonnegativity of likelihood factors
  have hLL : ∀ (b : Bool) (s : Fin n) (y : Fin T → Bool) (k : Fin T), 0 ≤ LL M α π b s k y := by
    intro b s y k
    have hin := histAt_inPrice M μ sig α π hπ s y k (by omega)
    have hp : priceAt π s y k ∈ M.price := by
      simp only [priceAt, Pricing.at, k.isLt, dif_pos]
      exact (hπ k _ hin).1
    have ha : promoAt α π b s y k ∈ Set.Icc (0:ℝ) 1 := by
      simp only [promoAt, Promo.at, k.isLt, dif_pos]; exact hα _ _ _ _
    exact likelihood_nonneg M hM b _ _ ha hp _
  have hPP : ∀ (b : Bool) (s : Fin n) (y : Fin T → Bool) (k : ℕ), 0 ≤ PP M α π b s k y := by
    intro b s y k
    unfold PP
    apply Finset.prod_nonneg
    intro i _
    split_ifs
    · exact hLL b s y i
    · exact zero_le_one
  -- belief relation
  have hrel : ∀ (s : Fin n) (y : Fin T → Bool) (k : ℕ), k ≤ T →
      belief M μ sig α k (histAt π s y k) *
        (μ * sig true s * PP M α π true s k y + (1 - μ) * sig false s * PP M α π false s k y) =
        μ * sig true s * PP M α π true s k y := by
    intro s y k
    induction k with
    | zero =>
      intro _
      simp only [PP_zero, mul_one, belief, histAt]
      have := bayes_rel μ μ 1 (sig true s) (sig false s) hμa (by linarith) (hsig.1 _ _)
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
      have hN : 0 ≤ μ * sig true s * PP M α π true s k y :=
        mul_nonneg (mul_nonneg hμa (hsig.1 _ _)) (hPP _ _ _ _)
      have hDN : 0 ≤ (1 - μ) * sig false s * PP M α π false s k y :=
        mul_nonneg (mul_nonneg (by linarith) (hsig.1 _ _)) (hPP _ _ _ _)
      have := bayes_rel (belief M μ sig α k (histAt π s y k))
        (μ * sig true s * PP M α π true s k y)
        (μ * sig true s * PP M α π true s k y + (1 - μ) * sig false s * PP M α π false s k y)
        (LL M α π true s kk y) (LL M α π false s kk y) hN (by linarith) (hLL _ _ _ _)
        (hLL _ _ _ _) hih
      linear_combination this
  -- the expectation in two forms
  have hexp : ∀ F : Bool → Fin n → (Fin T → Bool) → ℝ,
      ConfoundPromo.LongRun.expect M μ sig α π F =
        μ * ∑ s, sig true s * ∑ y, pathProb M α π true s y * F true s y +
        (1 - μ) * ∑ s, sig false s * ∑ y, pathProb M α π false s y * F false s y := by
    intro F
    simp [ConfoundPromo.LongRun.expect, condExpect, prior]
  set w : Bool × Fin n × (Fin T → Bool) → ℝ :=
    fun x => prior μ x.1 * sig x.1 x.2.1 * pathProb M α π x.1 x.2.1 x.2.2 with hw
  have hsum : ∀ F : Bool → Fin n → (Fin T → Bool) → ℝ,
      ConfoundPromo.LongRun.expect M μ sig α π F = ∑ x, w x * F x.1 x.2.1 x.2.2 := by
    intro F
    simp only [ConfoundPromo.LongRun.expect, condExpect, hw, Fintype.sum_prod_type,
      Finset.mul_sum, mul_assoc]
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    simp only [hw]
    apply mul_nonneg (mul_nonneg _ (hsig.1 _ _))
    · rw [← PP_T]; exact hPP _ _ _ _
    · unfold prior; split_ifs <;> linarith
  have hw1 : ∑ x, w x = 1 := by
    have := hsum (fun _ _ _ => 1)
    simp only [mul_one] at this
    rw [← this, hexp]
    simp only [mul_one, sum_PP_T, hsig.2]
    ring
  have hmono : ∀ F G : Bool → Fin n → (Fin T → Bool) → ℝ, (∀ b s y, F b s y ≤ G b s y) →
      ConfoundPromo.LongRun.expect M μ sig α π F ≤ ConfoundPromo.LongRun.expect M μ sig α π G := by
    intro F G h
    rw [hsum, hsum]
    apply Finset.sum_le_sum
    intro x _
    exact mul_le_mul_of_nonneg_left (h _ _ _) (hw0 x)
  have hlin : ∀ (F G : Bool → Fin n → (Fin T → Bool) → ℝ) (c : ℝ),
      ConfoundPromo.LongRun.expect M μ sig α π (fun b s y => F b s y + c + G b s y) =
        ConfoundPromo.LongRun.expect M μ sig α π F + c +
          ConfoundPromo.LongRun.expect M μ sig α π G := by
    intro F G c
    rw [hsum, hsum, hsum]
    have hc : ∑ x, w x * c = c := by rw [← Finset.sum_mul, hw1, one_mul]
    calc ∑ x, w x * (F x.1 x.2.1 x.2.2 + c + G x.1 x.2.1 x.2.2)
        = ∑ x, w x * F x.1 x.2.1 x.2.2 + ∑ x, w x * c + ∑ x, w x * G x.1 x.2.1 x.2.2 := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro x _; ring
      _ = _ := by rw [hc]
  have hsumT : ∀ F : Fin T → Bool → Fin n → (Fin T → Bool) → ℝ,
      ConfoundPromo.LongRun.expect M μ sig α π (fun b s y => ∑ t, F t b s y) =
        ∑ t, ConfoundPromo.LongRun.expect M μ sig α π (F t) := by
    intro F
    rw [hsum]
    simp only [hsum, Finset.mul_sum]
    rw [Finset.sum_comm]
  -- tower property for one period
  have htower : ∀ t : Fin T,
      ConfoundPromo.LongRun.expect M μ sig α π
          (fun b s y => surplus M b (promoAt α π b s y t) (priceAt π s y t)) =
        ConfoundPromo.LongRun.expect M μ sig α π
          (fun _ s y => periodSurplus M μ sig α π t (histAt π s y t)) := by
    intro t
    set F : Bool → Fin n → (Fin T → Bool) → ℝ :=
      fun b s y => surplus M b (promoAt α π b s y t) (priceAt π s y t) with hF
    set G : Fin n → (Fin T → Bool) → ℝ :=
      fun s y => periodSurplus M μ sig α π t (histAt π s y t) with hG
    have hdF : ∀ b s, Dep (T := T) t (F b s) := by
      intro b s y y' h
      simp only [hF, promoAt, priceAt]
      rw [histAt_dep π s y y' t h]
    have hdG : ∀ s, Dep (T := T) t (G s) := by
      intro s y y' h
      simp only [hG]
      rw [histAt_dep π s y y' t h]
    have hmarg : ∀ (b : Bool) (s : Fin n) (H : (Fin T → Bool) → ℝ), Dep (T := T) t H →
        ∑ y, pathProb M α π b s y * H y = (1/2) ^ (T - t) * ∑ y, PP M α π b s t y * H y := by
      intro b s H hH
      rw [← marg_iter M α π b s t H hH T t.isLt.le le_rfl]
      apply Finset.sum_congr rfl; intro y _; rw [PP_T]
    have eF : ∀ b s, ∑ y, pathProb M α π b s y * F b s y =
        (1/2) ^ (T - t) * ∑ y, PP M α π b s t y * F b s y := fun b s => hmarg b s _ (hdF b s)
    have eG : ∀ b s, ∑ y, pathProb M α π b s y * G s y =
        (1/2) ^ (T - t) * ∑ y, PP M α π b s t y * G s y := fun b s => hmarg b s _ (hdG s)
    have hGF : ∀ s y, G s y = belief M μ sig α t (histAt π s y t) * F true s y +
        (1 - belief M μ sig α t (histAt π s y t)) * F false s y := by
      intro s y
      simp [hG, hF, periodSurplus, expSurplus, promoAt, priceAt, Promo.at, Pricing.at, t.isLt]
    show ConfoundPromo.LongRun.expect M μ sig α π F =
      ConfoundPromo.LongRun.expect M μ sig α π (fun _ s y => G s y)
    rw [hexp, hexp]
    simp only [eF, eG]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro y _
    rw [hGF s y]
    have := hrel s y t t.isLt.le
    linear_combination (-(1/2 : ℝ) ^ (T - t) * (F true s y - F false s y)) * this
  -- surplusT as a sum of period expectations
  have hST : surplusT M μ sig α π = ∑ t : Fin T, ConfoundPromo.LongRun.expect M μ sig α π
      (fun _ s y => periodSurplus M μ sig α π t (histAt π s y t)) := by
    unfold surplusT pathSurplus
    rw [hsumT (fun t b s y => surplus M b (promoAt α π b s y t) (priceAt π s y t))]
    exact Finset.sum_congr rfl (fun t _ => htower t)
  -- pointwise bound
  set g : Bool → ℝ → ℝ := fun b m => if b then 1 - m else m with hg
  set Ex : Fin n → (Fin T → Bool) → Fin T → Prop :=
    fun s y t => InExcess M (ε / 2) μ sig α π t (histAt π s y t) with hEx
  have hpt : ∀ (b : Bool) (s : Fin n) (y : Fin T → Bool) (t : Fin T),
      periodSurplus M μ sig α π t (histAt π s y t) ≤
        co (WC M) (belief M μ sig α t (histAt π s y t)) + ε / 2 +
          (if Ex s y t then Cbar * g b (belief M μ sig α t (histAt π s y t)) else 0) := by
    intro b s y t
    set h := histAt π s y t
    have hin := histAt_inPrice M μ sig α π hπ s y t t.isLt.le
    have hmem := belief_mem M hM μ ⟨hμa, hμb⟩ sig hsig α hα t h hin
    by_cases hE : Ex s y t
    · rw [if_pos hE]
      have hW : periodSurplus M μ sig α π t h ≤ Wmax M (belief M μ sig α t h) := by
        unfold Wmax periodSurplus
        apply le_csSup (Wmax_bdd M hM _ hmem)
        exact ⟨fun q b => α t q b h, π t h, fun q b => hα t q b h, hπ t h hin, rfl⟩
      have hco := le_co (Wmax M) _ (fun m hm => Wmax_le M hM m hm) _ hmem
      have hl4 := hC _ hmem
      cases b
      · simp only [hg, Bool.false_eq_true, if_false]
        linarith [hl4.1]
      · simp only [hg, if_true]
        linarith [hl4.2]
    · rw [if_neg hE]
      simp only [hEx, InExcess, not_lt] at hE
      linarith
  -- excess term
  have hreidx : ∀ (b : Bool) (s : Fin n) (y : Fin T → Bool),
      ∑ t : Fin T, (if Ex s y t then g b (belief M μ sig α t (histAt π s y t)) else 0) =
        ∑ m ∈ Finset.Icc 1 T, g b (hitBelief M (ε / 2) μ sig α π b s y m) := by
    intro b s y
    rw [reindex (Ex s y) (fun t => g b (belief M μ sig α t (histAt π s y t)))]
    apply Finset.sum_congr rfl
    intro m _
    unfold hitBelief
    have hrs : reachSet M (ε / 2) μ sig α π s y m = reach (Ex s y) m := rfl
    by_cases hne : (reach (Ex s y) m).Nonempty
    · rw [dif_pos hne]
      have hne' : (reachSet M (ε / 2) μ sig α π s y m).Nonempty := hrs ▸ hne
      rw [dif_pos hne']
      rfl
    · rw [dif_neg hne]
      have hne' : ¬ (reachSet M (ε / 2) μ sig α π s y m).Nonempty := hrs ▸ hne
      rw [dif_neg hne']
      cases b <;> simp [hg]
  have hcond_sum : ∀ (b : Bool) (H : ℕ → Fin n → (Fin T → Bool) → ℝ),
      condExpect M sig α π b (fun s y => ∑ m ∈ Finset.Icc 1 T, H m s y) =
        ∑ m ∈ Finset.Icc 1 T, condExpect M sig α π b (H m) := by
    intro b H
    unfold condExpect
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    rw [← Finset.mul_sum]; congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hexcess : ConfoundPromo.LongRun.expect M μ sig α π
      (fun b s y => ∑ t : Fin T,
        (if Ex s y t then Cbar * g b (belief M μ sig α t (histAt π s y t)) else 0)) ≤ K := by
    have e1 : ∀ b s y, ∑ t : Fin T,
        (if Ex s y t then Cbar * g b (belief M μ sig α t (histAt π s y t)) else 0) =
        Cbar * ∑ m ∈ Finset.Icc 1 T, g b (hitBelief M (ε / 2) μ sig α π b s y m) := by
      intro b s y
      rw [← hreidx b s y, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro t _
      split_ifs <;> simp
    simp only [e1]
    unfold ConfoundPromo.LongRun.expect
    simp only [Fintype.sum_bool]
    have hc : ∀ b : Bool, condExpect M sig α π b
        (fun s y => Cbar * ∑ m ∈ Finset.Icc 1 T, g b (hitBelief M (ε / 2) μ sig α π b s y m)) ≤
        Cbar * (χ * ∑ m ∈ Finset.Icc 1 T, r ^ m) := by
      intro b
      have hlinc : condExpect M sig α π b
          (fun s y => Cbar * ∑ m ∈ Finset.Icc 1 T, g b (hitBelief M (ε / 2) μ sig α π b s y m)) =
          Cbar * condExpect M sig α π b
            (fun s y => ∑ m ∈ Finset.Icc 1 T, g b (hitBelief M (ε / 2) μ sig α π b s y m)) := by
        unfold condExpect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro s _
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro y _
        ring
      rw [hlinc]
      apply mul_le_mul_of_nonneg_left _ hC0
      rw [hcond_sum b (fun m s y => g b (hitBelief M (ε / 2) μ sig α π b s y m)), Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hb3 := h3 T n sig α π hsig hα hsp hbb hπ m hm.1
      have hexp_r : Real.exp (-β * m) = r ^ m := by
        rw [hr, ← Real.exp_nat_mul]; ring_nf
      rw [hexp_r] at hb3
      cases b
      · simpa [hg] using hb3.1
      · simpa [hg] using hb3.2
    have hgeo := geom_bound r hr0.le hr1 T
    have hpT : 0 ≤ prior μ true := by simp [prior, hμa]
    have hpF : 0 ≤ prior μ false := by simp [prior]; linarith
    have hpsum : prior μ false + prior μ true = 1 := by simp [prior]
    have hcF := hc false
    have hcT := hc true
    have hX : Cbar * (χ * ∑ m ∈ Finset.Icc 1 T, r ^ m) ≤ K := by
      rw [hKdef, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hC0
      exact mul_le_mul_of_nonneg_left hgeo hχ.le
    calc prior μ true * condExpect M sig α π true _ + prior μ false * condExpect M sig α π false _
        ≤ prior μ true * (Cbar * (χ * ∑ m ∈ Finset.Icc 1 T, r ^ m)) +
          prior μ false * (Cbar * (χ * ∑ m ∈ Finset.Icc 1 T, r ^ m)) := by
          gcongr
      _ = Cbar * (χ * ∑ m ∈ Finset.Icc 1 T, r ^ m) := by
          rw [← add_mul, add_comm, hpsum, one_mul]
      _ ≤ K := hX
  -- Jensen (step (a) of (31))
  have hjen : ∀ t : Fin T, ConfoundPromo.LongRun.expect M μ sig α π
      (fun _ s y => co (WC M) (belief M μ sig α t (histAt π s y t))) ≤ co (WC M) μ :=
    fun t => ((step_31_a M hM).2 μ ⟨hμa, hμb⟩ T n sig α π hsig hα hπ t t.isLt.le).2
  -- assemble
  have key : surplusT M μ sig α π ≤ T * co (WC M) μ + T * (ε / 2) + K := by
    rw [hST]
    have hb : ∀ t : Fin T, ConfoundPromo.LongRun.expect M μ sig α π
        (fun _ s y => periodSurplus M μ sig α π t (histAt π s y t)) ≤
        co (WC M) μ + ε / 2 + ConfoundPromo.LongRun.expect M μ sig α π
          (fun b s y => if Ex s y t then Cbar * g b (belief M μ sig α t (histAt π s y t)) else 0) := by
      intro t
      calc _ ≤ ConfoundPromo.LongRun.expect M μ sig α π
            (fun b s y => co (WC M) (belief M μ sig α t (histAt π s y t)) + ε / 2 +
              (if Ex s y t then Cbar * g b (belief M μ sig α t (histAt π s y t)) else 0)) :=
            hmono _ _ (fun b s y => hpt b s y t)
        _ = ConfoundPromo.LongRun.expect M μ sig α π
              (fun _ s y => co (WC M) (belief M μ sig α t (histAt π s y t))) + ε / 2 +
            ConfoundPromo.LongRun.expect M μ sig α π
              (fun b s y => if Ex s y t then Cbar * g b (belief M μ sig α t (histAt π s y t)) else 0) :=
            hlin (fun _ s y => co (WC M) (belief M μ sig α t (histAt π s y t))) _ (ε / 2)
        _ ≤ _ := by linarith [hjen t]
    calc ∑ t : Fin T, ConfoundPromo.LongRun.expect M μ sig α π
            (fun _ s y => periodSurplus M μ sig α π t (histAt π s y t))
        ≤ ∑ t : Fin T, (co (WC M) μ + ε / 2 + ConfoundPromo.LongRun.expect M μ sig α π
          (fun b s y => if Ex s y t then Cbar * g b (belief M μ sig α t (histAt π s y t)) else 0)) :=
          Finset.sum_le_sum (fun t _ => hb t)
      _ = T * co (WC M) μ + T * (ε / 2) + ConfoundPromo.LongRun.expect M μ sig α π
            (fun b s y => ∑ t : Fin T,
              (if Ex s y t then Cbar * g b (belief M μ sig α t (histAt π s y t)) else 0)) := by
          rw [hsumT (fun t b s y =>
            if Ex s y t then Cbar * g b (belief M μ sig α t (histAt π s y t)) else 0)]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ T * co (WC M) μ + T * (ε / 2) + K := by linarith [hexcess]
  rw [div_lt_iff₀ hTpos]
  nlinarith [key, hKT]
