-- Prove2me | solution 1 for CountingLLL.DetCount.approximation_from_estimator
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:51:40.909083+00:00
-- url     : https://prove2.me/submissions/f05e2b2d-b526-4766-a474-4bef83fc8521

import Mathlib
import Theorems.Thm_CountingLLL_DetCount_equation_21
import Theorems.Thm_CountingLLL_DetCount_lemma_3_1
import Theorems.Thm_CountingLLL_DetCount_lemma_4_3
set_option autoImplicit false
open scoped BigOperators

/-- Multiplicative errors in positive factors accumulate at most linearly at small total error. -/
private theorem product_relative_error {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (δ ε : ℝ)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs : (s.card : ℝ)*δ ≤ ε/4)
    (hb : ∀ i ∈ s, 0 ≤ b i)
    (ha : ∀ i ∈ s, |a i - b i| ≤ δ*b i) :
    (1-ε)*(∏ i ∈ s, b i) ≤ ∏ i ∈ s, a i ∧
      (∏ i ∈ s, a i) ≤ (1+ε)*(∏ i ∈ s, b i) := by
  classical
  by_cases hempty : s = ∅
  · subst s
    simp only [Finset.prod_empty, mul_one]
    constructor <;> linarith
  have hspos : (0:ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  have hsone : (1:ℝ) ≤ s.card := by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
  have hδ1 : δ ≤ 1 := by
    have := mul_nonneg hδ (sub_nonneg.mpr hsone)
    nlinarith
  have hlower (i : ι) (hi : i ∈ s) : (1-δ)*b i ≤ a i := by
    have hh := (abs_le.mp (ha i hi)).1
    nlinarith
  have hupper (i : ι) (hi : i ∈ s) : a i ≤ (1+δ)*b i := by
    have hh := (abs_le.mp (ha i hi)).2
    nlinarith
  have hbprod : 0 ≤ ∏ i ∈ s, b i := Finset.prod_nonneg hb
  have ha0 (i : ι) (hi : i ∈ s) : 0 ≤ a i :=
    le_trans (mul_nonneg (by linarith) (hb i hi)) (hlower i hi)
  have hlo : (1-δ)^s.card*(∏ i ∈ s, b i) ≤ ∏ i ∈ s, a i := by
    have hh := Finset.prod_le_prod (f := fun i => (1-δ)*b i) (g := a)
      (fun i hi => mul_nonneg (by linarith) (hb i hi)) hlower
    simpa [Finset.prod_mul_distrib] using hh
  have hhi : (∏ i ∈ s, a i) ≤ (1+δ)^s.card*(∏ i ∈ s, b i) := by
    have hh := Finset.prod_le_prod (f := a) (g := fun i => (1+δ)*b i) ha0 hupper
    simpa [Finset.prod_mul_distrib] using hh
  have hpowlo : 1-ε ≤ (1-δ)^s.card := by
    have hh := one_add_mul_le_pow (a := -δ) (by linarith : (-2:ℝ) ≤ -δ) s.card
    simp only [mul_neg, ← sub_eq_add_neg] at hh
    linarith
  have hexp : (1+δ)^s.card ≤ Real.exp ((s.card : ℝ)*δ) := by
    calc
      (1+δ)^s.card ≤ (Real.exp δ)^s.card := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp δ]) _
      _ = Real.exp ((s.card : ℝ)*δ) := by rw [Real.exp_nat_mul]
  have hx : 0 ≤ (s.card : ℝ)*δ := mul_nonneg (by positivity) hδ
  have hxs : (s.card : ℝ)*δ ≤ 1/4 := by linarith
  have hexpbound : Real.exp ((s.card : ℝ)*δ) ≤ 1+ε := by
    have hx2 : (s.card : ℝ)*δ < 2 := by linarith
    have hrat := Real.exp_le_two_add_div_two_sub hx hx2
    have hden : 0 < 2-(s.card : ℝ)*δ := by linarith
    have hrat' : (2+(s.card : ℝ)*δ)/(2-(s.card : ℝ)*δ) ≤ 1+ε := by
      apply (div_le_iff₀ hden).2
      have hh := mul_nonneg hε (sub_nonneg.mpr hxs)
      nlinarith
    exact hrat.trans hrat'
  exact ⟨(mul_le_mul_of_nonneg_right hpowlo hbprod).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_right (hexp.trans hexpbound) hbprod)⟩
set_option autoImplicit false
open scoped Classical BigOperators
open CountingLLL.DetCount CountingLLL.DetCount.CSP

private theorem pmax_small (Φ : CSP) (hΦ : Φ.Condition11) : Φ.pmax ≤ 0.1 := by
  have hp : 0 ≤ Φ.pmax := NNReal.coe_nonneg _
  have he : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hd : (0 : ℝ) ≤ Φ.Dmax := Nat.cast_nonneg _
  have hA : 1 ≤ ((Φ.Dmax : ℝ)+1)^2 := by nlinarith [sq_nonneg (Φ.Dmax : ℝ)]
  have hpA : Φ.pmax ≤ Φ.pmax * ((Φ.Dmax : ℝ)+1)^2 := by
    nlinarith [mul_nonneg hp (show 0 ≤ ((Φ.Dmax : ℝ)+1)^2 - 1 by linarith)]
  unfold CSP.Condition11 at hΦ
  nlinarith [mul_nonneg (show 0 ≤ 4*Real.exp 1 - 10 by linarith) hp]

/-- The telescoped truncated marginals approximate the full partition function. -/
theorem solution (Φ : CSP) (hΦ : Φ.Condition11)
    (L : ℕ) (en : Φ.EnumChoice) (hen : Φ.ValidEnum en) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hL : (Φ.m : ℝ) * (8*(0.9 : ℝ)^L) ≤ ε/4) :
    let Cpre : ℕ → Finset (Fin Φ.m) :=
      fun i => Finset.univ.filter (fun j : Fin Φ.m => j.val < i)
    let Zhat : ℝ := (∏ v, (Φ.q v : ℝ)) *
      ∏ i : Fin Φ.m, (1 - Φ.rhatWith en L (Cpre (i.val+1)) i)
    (1-ε)*(Φ.ZPhi : ℝ) ≤ Zhat ∧ Zhat ≤ (1+ε)*(Φ.ZPhi : ℝ) := by
  classical
  dsimp only
  let Cpre : ℕ → Finset (Fin Φ.m) :=
    fun i => Finset.univ.filter (fun j : Fin Φ.m => j.val < i)
  let A : Fin Φ.m → ℝ := fun i => 1 - Φ.rhatWith en L (Cpre (i.val+1)) i
  let B : Fin Φ.m → ℝ := fun i => 1 - Φ.r (Cpre (i.val+1)) i
  have hmem (i : Fin Φ.m) : i ∈ Cpre (i.val+1) := by simp [Cpre]
  have hB (i : Fin Φ.m) : (1/2 : ℝ) ≤ B i := by
    have h := lemma_3_1 Φ hΦ (Cpre (i.val+1)) i (hmem i)
    have hp := pmax_small Φ hΦ
    dsimp [B]
    linarith
  have hpow : 0 ≤ (0.9 : ℝ)^L := by positivity
  have herr (i : Fin Φ.m) : |A i-B i| ≤ (8*(0.9 : ℝ)^L)*B i := by
    have h := (lemma_4_3 Φ hΦ (Cpre (i.val+1)) i (hmem i) L en hen).2.2
    have heq : A i - B i = -(Φ.rhatWith en L (Cpre (i.val+1)) i - Φ.r (Cpre (i.val+1)) i) := by dsimp [A,B]; ring
    rw [heq, abs_neg]
    have hh := mul_nonneg hpow (show 0 ≤ B i - 1/2 by linarith [hB i])
    nlinarith
  have happrox := product_relative_error (Finset.univ : Finset (Fin Φ.m)) A B
    (8*(0.9 : ℝ)^L) ε (by positivity) hε hε1 (by simpa using hL)
    (fun i _ => le_trans (by norm_num) (hB i)) (fun i _ => herr i)
  have hq : 0 ≤ ∏ v, (Φ.q v : ℝ) := Finset.prod_nonneg (fun _ _ => by positivity)
  have heq := (equation_21 Φ hΦ (Equiv.refl _)).1.trans
    ((equation_21 Φ hΦ (Equiv.refl _)).2.1.trans (equation_21 Φ hΦ (Equiv.refl _)).2.2)
  have heq' : (Φ.ZPhi : ℝ) = (∏ v, (Φ.q v : ℝ)) * ∏ i, B i := by
    simpa [B,Cpre] using heq
  constructor
  · rw [heq']
    have h := mul_le_mul_of_nonneg_left happrox.1 hq
    simpa [A,Cpre, mul_assoc, mul_left_comm, mul_comm] using h
  · rw [heq']
    have h := mul_le_mul_of_nonneg_left happrox.2 hq
    simpa [A,Cpre, mul_assoc, mul_left_comm, mul_comm] using h
