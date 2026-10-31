-- Prove2me | solution 1 for ConfoundPromo.LongRun.step_31_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T07:45:04.500637+00:00
-- url     : https://prove2.me/submissions/ee90748b-e4c7-4814-8287-e77496e140fc

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

open ConfoundPromo.LongRun
open Finset

namespace CPSol31a

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

end CPSol31a

namespace CPSol31a

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

end CPSol31a

open CPSol31a

theorem solution (M : Market) (hM : M.Standing) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (co (WC M)) ∧
    ∀ (μ0 : ℝ), μ0 ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (T n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T),
        sig.IsValid → α.IsValid → IsMyopic M μ0 sig α π → ∀ t : ℕ, t ≤ T →
          ConfoundPromo.LongRun.expect M μ0 sig α π (fun _ s y => belief M μ0 sig α t (histAt π s y t)) = μ0 ∧
          ConfoundPromo.LongRun.expect M μ0 sig α π (fun _ s y => co (WC M) (belief M μ0 sig α t (histAt π s y t)))
            ≤ co (WC M) μ0 := by
  have hconc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (co (WC M)) :=
    co_concave (WC M) _ (fun μ hμ => WC_le M hM μ hμ)
  refine ⟨hconc, ?_⟩
  intro μ0 hμ0 T n sig α π hsig hα hπ t ht
  obtain ⟨hμa, hμb⟩ := hμ0
  -- nonnegativity of likelihood factors
  have hLL : ∀ (b : Bool) (s : Fin n) (y : Fin T → Bool) (k : Fin T), 0 ≤ LL M α π b s k y := by
    intro b s y k
    have hin := histAt_inPrice M μ0 sig α π hπ s y k (by omega)
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
  set μt : Fin n → (Fin T → Bool) → ℝ := fun s y => belief M μ0 sig α t (histAt π s y t) with hμt
  -- belief relation
  have hrel : ∀ (s : Fin n) (y : Fin T → Bool) (k : ℕ), k ≤ T →
      belief M μ0 sig α k (histAt π s y k) *
        (μ0 * sig true s * PP M α π true s k y + (1 - μ0) * sig false s * PP M α π false s k y) =
        μ0 * sig true s * PP M α π true s k y := by
    intro s y k
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
  have hdepμ : ∀ s, Dep (T := T) t (μt s) := by
    intro s y y' h
    simp only [hμt]
    rw [histAt_dep π s y y' t h]
  -- the expectation as a single sum
  have hexp : ∀ F : Bool → Fin n → (Fin T → Bool) → ℝ,
      ConfoundPromo.LongRun.expect M μ0 sig α π F =
        μ0 * ∑ s, sig true s * ∑ y, pathProb M α π true s y * F true s y +
        (1 - μ0) * ∑ s, sig false s * ∑ y, pathProb M α π false s y * F false s y := by
    intro F
    simp [ConfoundPromo.LongRun.expect, condExpect, prior]
  have hmarg : ∀ (b : Bool) (s : Fin n) (G : (Fin T → Bool) → ℝ), Dep (T := T) t G →
      ∑ y, pathProb M α π b s y * G y = (1/2) ^ (T - t) * ∑ y, PP M α π b s t y * G y := by
    intro b s G hG
    rw [← marg_iter M α π b s t G hG T ht le_rfl]
    apply Finset.sum_congr rfl; intro y _; rw [PP_T]
  -- martingale
  have hmart : ConfoundPromo.LongRun.expect M μ0 sig α π (fun _ s y => μt s y) = μ0 := by
    rw [hexp]
    simp only [hmarg _ _ _ (hdepμ _)]
    have step : ∀ s, μ0 * (sig true s * ((1/2) ^ (T - t) * ∑ y, PP M α π true s t y * μt s y)) +
        (1 - μ0) * (sig false s * ((1/2) ^ (T - t) * ∑ y, PP M α π false s t y * μt s y)) =
        μ0 * (sig true s * ((1/2) ^ (T - t) * ∑ y, PP M α π true s t y * 1)) := by
      intro s
      have : ∀ y, μ0 * sig true s * PP M α π true s t y * μt s y +
          (1 - μ0) * sig false s * PP M α π false s t y * μt s y =
          μ0 * sig true s * PP M α π true s t y * 1 := by
        intro y
        have := hrel s y t ht
        simp only [hμt]
        linear_combination this
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      have hs' : ∀ y, μ0 * (sig true s * ((1/2) ^ (T - t) * (PP M α π true s t y * μt s y))) +
          (1 - μ0) * (sig false s * ((1/2) ^ (T - t) * (PP M α π false s t y * μt s y))) =
          μ0 * (sig true s * ((1/2) ^ (T - t) * (PP M α π true s t y * 1))) := by
        intro y
        have := this y
        linear_combination (1/2 : ℝ) ^ (T - t) * this
      exact Finset.sum_congr rfl (fun y _ => hs' y)
    have hone : ∀ s, (1/2 : ℝ) ^ (T - t) * ∑ y, PP M α π true s t y = 1 := by
      intro s
      have := hmarg true s (fun _ => 1) (fun _ _ _ => rfl)
      simp only [mul_one] at this
      rw [← this]
      exact sum_PP_T M α π true s
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun s _ => step s)]
    simp only [hone, mul_one]
    rw [← Finset.mul_sum, hsig.2 true, mul_one]
  refine ⟨hmart, ?_⟩
  -- Jensen
  set w : Bool × Fin n × (Fin T → Bool) → ℝ :=
    fun x => prior μ0 x.1 * sig x.1 x.2.1 * pathProb M α π x.1 x.2.1 x.2.2 with hw
  have hsum : ∀ F : Bool → Fin n → (Fin T → Bool) → ℝ,
      ConfoundPromo.LongRun.expect M μ0 sig α π F = ∑ x, w x * F x.1 x.2.1 x.2.2 := by
    intro F
    simp only [ConfoundPromo.LongRun.expect, condExpect, hw, Fintype.sum_prod_type,
      Finset.mul_sum, mul_assoc]
  have hw0 : ∀ x ∈ (Finset.univ : Finset (Bool × Fin n × (Fin T → Bool))), 0 ≤ w x := by
    intro x _
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
  have hmem : ∀ x ∈ (Finset.univ : Finset (Bool × Fin n × (Fin T → Bool))),
      μt x.2.1 x.2.2 ∈ Set.Icc (0:ℝ) 1 := by
    intro x _
    exact belief_mem M hM μ0 ⟨hμa, hμb⟩ sig hsig α hα t _
      (histAt_inPrice M μ0 sig α π hπ x.2.1 x.2.2 t ht)
  have hJ := hconc.le_map_sum hw0 hw1 hmem
  simp only [smul_eq_mul] at hJ
  have h2 := hsum (fun _ s y => μt s y)
  rw [hmart] at h2
  rw [← h2] at hJ
  rw [hsum]
  exact hJ
