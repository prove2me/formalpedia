-- Prove2me | solution 1 for DynamicOnlineLP.LowerBound.lemma11
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T05:54:02.939213+00:00
-- url     : https://prove2.me/submissions/20b6b529-5c1e-479f-887c-f732b1dd9c82

import Mathlib.Data.Real.Sqrt
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Theorems.Thm_EthierKurtz_cramer_weighted_rademacher_sums
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Finite exceptional-range helpers for DynamicOnlineLP.LowerBound.lemma11.
The uniform proof uses the verified published Cramér bound. Development checks are pending.
-/

namespace Lemma11Proof

open Finset

def ones {n : ℕ} (y : Fin n → Bool) : ℕ := (univ.filter (fun j ↦ y j = true)).card

def balanced (r : ℕ) : Fin r → Bool := fun j ↦ decide (j.val < r / 2)

lemma ones_balanced (r : ℕ) : ones (balanced r) = r / 2 := by
  classical
  let S : Finset (Fin r) := univ.filter (fun j ↦ j.val < r / 2)
  let e : ↥S ≃ Fin (r / 2) := {
    toFun := fun j ↦ ⟨j.val.val, by exact (Finset.mem_filter.mp j.property).2⟩
    invFun := fun j ↦ ⟨⟨j.val, lt_of_lt_of_le j.isLt (Nat.div_le_self _ _)⟩,
      by simp [S, j.isLt]⟩
    left_inv := by intro j; apply Subtype.ext; apply Fin.ext; rfl
    right_inv := by intro j; apply Fin.ext; rfl }
  have hc : S.card = r / 2 := by
    rw [← Fintype.card_coe]
    exact (Fintype.card_congr e).trans (Fintype.card_fin _)
  simpa [ones, balanced, S] using hc

lemma deviation_le_half (k : ℕ) (hk : 2 ≤ k) : ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ k / 2 := by
  apply Nat.ceil_le.mpr
  have hq : 1 ≤ k / 2 := by omega
  have hkr : k ≤ 2 * (k / 2) + 1 := by omega
  have hq' : (1 : ℝ) ≤ (k / 2 : ℕ) := by exact_mod_cast hq
  have hkr' : (k : ℝ) ≤ 2 * (k / 2 : ℕ) + 1 := by exact_mod_cast hkr
  have hs := Real.sq_sqrt (Nat.cast_nonneg k)
  have hs' := Real.sqrt_nonneg (k : ℝ)
  nlinarith [sq_nonneg ((k / 2 : ℕ) - (1 : ℝ))]

lemma nonempty_fraction_ge {n N : ℕ} (hn : n ≤ 2 * N + 2)
    (E : Finset (Fin n → Bool)) (hE : E.Nonempty) :
    1 / (2 : ℝ) ^ (2 * N + 2) ≤ (E.card : ℝ) / 2 ^ n := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hpow : (2 : ℝ) ^ n ≤ 2 ^ (2 * N + 2) := pow_le_pow_right₀ (by norm_num) hn
  have hc : (1 : ℝ) ≤ E.card := by exact_mod_cast one_le_card.mpr hE
  calc 1 / (2 : ℝ) ^ (2 * N + 2) ≤ 1 / (2 : ℝ) ^ n :=
        one_div_le_one_div_of_le hp hpow
    _ ≤ (E.card : ℝ) / 2 ^ n := div_le_div_of_nonneg_right hc hp.le

lemma bounded_lemma11 (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ k r : ℕ, 2 ≤ k → k ≤ N → r ≤ k →
      c ≤ ((univ.filter (fun y : Fin r → Bool ↦
            c ≤ ((univ.filter (fun u : Fin (2 * k - r) → Bool ↦
                    k + ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ ones y + ones u)).card : ℝ) /
                  2 ^ (2 * k - r) ∧
            c ≤ ((univ.filter (fun u : Fin (2 * k - r) → Bool ↦
                    ones y + ones u + ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ k)).card : ℝ) /
                  2 ^ (2 * k - r))).card : ℝ) / 2 ^ r := by
  classical
  let c : ℝ := 1 / (2 : ℝ) ^ (2 * N + 2)
  refine ⟨c, by dsimp [c]; positivity, ?_, ?_⟩
  · dsimp [c]
    apply (div_lt_one (by positivity)).2
    exact one_lt_pow₀ (by norm_num) (by omega)
  · intro k r hk hN hr
    have hd := deviation_le_half k hk
    have hhigh : k + ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ r / 2 + (2 * k - r) := by omega
    have hlow : r / 2 + ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ k := by omega
    apply nonempty_fraction_ge (by omega)
    refine ⟨balanced r, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · apply nonempty_fraction_ge (by omega)
      refine ⟨fun _ ↦ true, ?_⟩
      simp only [mem_filter, mem_univ, true_and]
      rw [ones_balanced]
      simpa [ones] using hhigh
    · apply nonempty_fraction_ge (by omega)
      refine ⟨fun _ ↦ false, ?_⟩
      simp only [mem_filter, mem_univ, true_and]
      rw [ones_balanced]
      simpa [ones] using hlow

/-! Standard-normal positivity facts, adapted from the already accepted Cramér proof. -/
section Gaussian
open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

noncomputable def phi (t : ℝ) : ℝ := (√(2 * π))⁻¹ * rexp (-(t ^ 2 / 2))

lemma phi_pos (t : ℝ) : 0 < phi t := by unfold phi; positivity

lemma gaussianPDFReal_std (t : ℝ) : gaussianPDFReal 0 1 t = phi t := by
  simp [gaussianPDFReal_def, phi, neg_div]

lemma continuous_phi : Continuous phi := by unfold phi; fun_prop

lemma integrable_phi : Integrable phi := by
  have := integrable_gaussianPDFReal 0 1
  simpa [funext gaussianPDFReal_std] using this

lemma cdf_std_eq (x : ℝ) : cdf (gaussianReal 0 1) x = ∫ t in Iic x, phi t := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
      (fun t _ => gaussianPDFReal_nonneg _ _ t))]
  simp [gaussianPDFReal_std]

lemma integral_phi : ∫ t, phi t = 1 := by
  have := integral_gaussianPDFReal_eq_one 0 (v := 1) one_ne_zero
  simpa [funext gaussianPDFReal_std] using this

lemma one_sub_cdf_std (x : ℝ) : 1 - cdf (gaussianReal 0 1) x = ∫ t in Ioi x, phi t := by
  rw [cdf_std_eq, ← integral_phi, ← integral_add_compl (measurableSet_Iic (a := x)) integrable_phi,
    compl_Iic]
  ring

lemma phi_neg (t : ℝ) : phi (-t) = phi t := by simp [phi]

lemma cdf_std_neg (x : ℝ) : cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  rw [cdf_std_eq, one_sub_cdf_std]
  have : ∫ t in Iic (-x), phi t = ∫ t in Iic (-x), phi (-t) := by simp_rw [phi_neg]
  rw [this, integral_comp_neg_Iic, neg_neg]

lemma cdf_std_pos (x : ℝ) : 0 < cdf (gaussianReal 0 1) x := by
  rw [cdf_std_eq]
  have hsupp : Function.support phi = univ := by ext t; simp [(phi_pos t).ne']
  have hpos : 0 < volume (Function.support phi ∩ Iic x) := by
    rw [hsupp, univ_inter, Real.volume_Iic]; exact ENNReal.zero_lt_top
  exact (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun t => (phi_pos t).le)
    integrable_phi.integrableOn).mpr hpos

lemma cdf_std_lt_one (x : ℝ) : cdf (gaussianReal 0 1) x < 1 := by
  have := cdf_std_pos (-x)
  rw [cdf_std_neg] at this
  linarith

lemma hasDerivAt_cdf_std (x : ℝ) :
    HasDerivAt (fun y => cdf (gaussianReal 0 1) y) (phi x) x := by
  have e : (fun y => cdf (gaussianReal 0 1) y)
      = fun y => (∫ t in Iic 0, phi t) + ∫ t in (0 : ℝ)..y, phi t := by
    funext y
    rw [cdf_std_eq, ← intervalIntegral.integral_Iic_sub_Iic integrable_phi.integrableOn
      integrable_phi.integrableOn]
    ring
  rw [e]
  exact ((continuous_phi.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _

lemma cdf_std_zero : cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  have := cdf_std_neg 0
  norm_num at this ⊢
  linarith

lemma cdf_std_two_gt_half : 1 / 2 < cdf (gaussianReal 0 1) 2 := by
  rw [← cdf_std_zero]
  exact (strictMono_of_hasDerivAt_pos hasDerivAt_cdf_std phi_pos) (by norm_num)

end Gaussian

noncomputable def score {n : ℕ} (y : Fin n → Bool) : ℝ :=
  ∑ j, if y j = true then -1 else 1

lemma score_eq {n : ℕ} (y : Fin n → Bool) : score y = n - 2 * (ones y : ℝ) := by
  classical
  have h j : (if y j = true then (-1 : ℝ) else 1) =
      1 - 2 * (if y j = true then 1 else 0) := by split_ifs <;> norm_num
  simp_rw [score, h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [ones]

lemma ones_le {n : ℕ} (y : Fin n → Bool) : ones y ≤ n := by
  exact (card_filter_le _ _).trans_eq (by simp)

noncomputable def tail (n : ℕ) (y s : ℝ) : Finset (Fin n → Bool) :=
  by classical exact univ.filter (fun e ↦ y * Real.sqrt (n : ℝ) < s * score e)

noncomputable def fraction {α : Type*} [Fintype α] (E : Finset α) : ℝ :=
  E.card / Fintype.card α

lemma fraction_cube {n : ℕ} (E : Finset (Fin n → Bool)) :
    fraction E = (E.card : ℝ) / 2 ^ n := by simp [fraction, Fintype.card_fun]

lemma cramer_sign_bounds :
    ∃ ε C N0 : ℝ, 0 < ε ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → N0 ≤ (n : ℝ) →
      ∀ y s : ℝ, s = 1 ∨ s = -1 → 0 ≤ y → y ≤ ε * Real.sqrt (n : ℝ) →
        (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) y) *
            Real.exp (-(C * ((y ^ 3 + 1) / Real.sqrt (n : ℝ)))) ≤ fraction (tail n y s) ∧
        fraction (tail n y s) ≤
          (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) y) *
            Real.exp (C * ((y ^ 3 + 1) / Real.sqrt (n : ℝ))) := by
  obtain ⟨ε, C, N0, hε, hC, h⟩ :=
    EthierKurtz.cramer_weighted_rademacher_sums 1 1 (by norm_num) (by norm_num)
  refine ⟨ε, C, N0, hε, hC, ?_⟩
  intro n hn hN y s hs hy hyε
  have hsquare : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have habs : ∀ i : Fin n, |(fun _ : Fin n ↦ s) i| ≤ 1 := by
    intro i; rcases hs with rfl | rfl <;> norm_num
  have hsum : (∑ _i : Fin n, s ^ 2) = (n : ℝ) := by simp [hsquare]
  have hvar : (1 : ℝ) * n ≤ ∑ _i : Fin n, s ^ 2 := by rw [hsum]; simp
  have hscore (e : Fin n → Bool) :
      (∑ i, (if e i = true then (-1 : ℝ) else 1) * s) = s * score e := by
    simp only [score, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hh := h n hn hN (fun _ ↦ s) habs hvar y hy hyε
  simp only [hscore, hsum, mul_div_cancel_right₀ _ hsqrt] at hh
  simpa only [fraction_cube, tail] using hh

open Filter

lemma eventual_tail_bounds :
    ∃ a p : ℝ, 0 < a ∧ a < 1 ∧ 0 < p ∧ ∃ N : ℕ, 1 ≤ N ∧
      (∀ n : ℕ, N ≤ n → ∀ s : ℝ, s = 1 ∨ s = -1 →
        p ≤ fraction (tail n 4 s)) ∧
      (∀ n : ℕ, N ≤ n → ∀ s : ℝ, s = 1 ∨ s = -1 →
        fraction (tail n 2 s) ≤ (1 - a) / 2) := by
  classical
  obtain ⟨ε, C, N0, hε, hC, h⟩ := cramer_sign_bounds
  let q : ℝ := 1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) 2
  have hq0 : 0 < q := sub_pos.mpr (cdf_std_lt_one 2)
  have hqh : q < 1 / 2 := by dsimp [q]; linarith [cdf_std_two_gt_half]
  let u : ℝ := (q + 1 / 2) / 2
  let a : ℝ := 1 - 2 * u
  let p : ℝ := (1 - ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) 4) *
    Real.exp (-(65 * C))
  have ha : 0 < a := by dsimp [a, u]; linarith
  have ha1 : a < 1 := by dsimp [a, u]; linarith
  have hp : 0 < p := mul_pos (sub_pos.mpr (cdf_std_lt_one 4)) (Real.exp_pos _)
  have hsqrt : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Filter.Tendsto (fun n : ℕ ↦ q * Real.exp (C * ((2 ^ 3 + 1) / Real.sqrt (n : ℝ))))
      Filter.atTop (nhds q) := by
    have hh := (((tendsto_inv_atTop_zero.comp hsqrt).const_mul (C * (2 ^ 3 + 1))).rexp).const_mul q
    simpa [div_eq_mul_inv, mul_assoc] using hh
  have hupper : ∀ᶠ n : ℕ in Filter.atTop,
      q * Real.exp (C * ((2 ^ 3 + 1) / Real.sqrt (n : ℝ))) ≤ u :=
    hlim.eventually_le_const (by dsimp [u]; linarith)
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ n ∧ N0 ≤ (n : ℝ) ∧ 4 ≤ ε * Real.sqrt (n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) _ _).eventually
        (Filter.eventually_ge_atTop N0),
      (hsqrt.const_mul_atTop hε).eventually (Filter.eventually_ge_atTop 4)] with n hn hN hy
    exact ⟨hn, hN, hy⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hupper.and hlarge)
  refine ⟨a, p, ha, ha1, hp, max N 1, le_max_right _ _, ?_, ?_⟩
  · intro n hn s hs
    have hnN := (le_max_left N 1).trans hn
    obtain ⟨hu, hn1, hN0, hy⟩ := hN n hnN
    have hl := (h n hn1 hN0 4 s hs (by norm_num) hy).1
    apply le_trans ?_ hl
    dsimp [p]
    apply mul_le_mul_of_nonneg_left _ (sub_pos.mpr (cdf_std_lt_one 4)).le
    apply Real.exp_le_exp.mpr
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hr : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := (Real.one_le_sqrt).mpr hnreal
    have hdiv : (65 : ℝ) / Real.sqrt (n : ℝ) ≤ 65 :=
      (div_le_self (by norm_num) hr)
    norm_num only [Nat.reduceAdd, Nat.reducePow] at hl ⊢
    nlinarith [mul_le_mul_of_nonneg_left hdiv hC.le]
  · intro n hn s hs
    obtain ⟨hu, hn1, hN0, hy⟩ := hN n ((le_max_left N 1).trans hn)
    have hh := (h n hn1 hN0 2 s hs (by norm_num) (by linarith)).2
    have hua : u = (1 - a) / 2 := by dsimp [a]; ring
    exact hh.trans (by simpa only [← hua] using hu)

lemma fraction_mono {n : ℕ} {E F : Finset (Fin n → Bool)} (h : E ⊆ F) :
    fraction E ≤ fraction F := by
  rw [fraction_cube, fraction_cube]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card h) (by positivity)

lemma fraction_univ_cube (n : ℕ) : fraction (univ : Finset (Fin n → Bool)) = 1 := by
  simp [fraction]

noncomputable def central (n : ℕ) (v : ℝ) : Finset (Fin n → Bool) :=
  by classical exact univ.filter (fun y ↦ -2 * v ≤ score y ∧ score y ≤ 2 * v)

lemma central_fraction_ge {n : ℕ} {a : ℝ}
    (hp : fraction (tail n 2 1) ≤ (1 - a) / 2)
    (hm : fraction (tail n 2 (-1)) ≤ (1 - a) / 2) :
    a ≤ fraction (central n (Real.sqrt (n : ℝ))) := by
  classical
  let E := central n (Real.sqrt (n : ℝ))
  let P := tail n 2 1
  let M := tail n 2 (-1)
  have hcover : (univ : Finset (Fin n → Bool)) ⊆ E ∪ (P ∪ M) := by
    intro y hy
    simp only [mem_union, E, central, mem_filter, mem_univ, true_and, P, M, tail]
    by_cases h₁ : -2 * Real.sqrt (n : ℝ) ≤ score y
    · by_cases h₂ : score y ≤ 2 * Real.sqrt (n : ℝ)
      · exact Or.inl ⟨h₁, h₂⟩
      · exact Or.inr (Or.inl (by simp only [one_mul]; linarith))
    · exact Or.inr (Or.inr (by simp only [neg_one_mul]; linarith))
  have hc : (2 : ℝ) ^ n ≤ (E.card : ℝ) + P.card + M.card := by
    have hh := (card_le_card hcover).trans
      ((card_union_le E (P ∪ M)).trans (Nat.add_le_add_left (card_union_le P M) _))
    have hh' : 2 ^ n ≤ E.card + P.card + M.card := by
      simpa [Fintype.card_fun, Nat.add_assoc] using hh
    exact_mod_cast hh'
  rw [fraction_cube] at hp hm ⊢
  have hd : (0 : ℝ) < 2 ^ n := by positivity
  have hp' := (div_le_iff₀ hd).mp hp
  have hm' := (div_le_iff₀ hd).mp hm
  apply (le_div_iff₀ hd).mpr
  change a * 2 ^ n ≤ (E.card : ℝ)
  change (P.card : ℝ) ≤ _ at hp'
  change (M.card : ℝ) ≤ _ at hm'
  nlinarith

lemma ceil_half_le_sqrt (k : ℕ) (hk : 4 ≤ k) :
    (⌈Real.sqrt (k : ℝ) / 2⌉₊ : ℝ) ≤ Real.sqrt (k : ℝ) := by
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : (2 : ℝ) ≤ Real.sqrt (k : ℝ) :=
    (Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)).mpr (by norm_num; exact hk)
  have hd := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt (k : ℝ) / 2 by positivity)
  linarith

lemma central_large_capacity {N k r : ℕ} {a : ℝ} (ha : a ≤ 1)
    (hN : 1 ≤ N) (hk : N * N ≤ k) (hr : r ≤ k)
    (hcentral : ∀ n : ℕ, N ≤ n → a ≤ fraction (central n (Real.sqrt (n : ℝ)))) :
    a ≤ fraction (central r (Real.sqrt (k : ℝ))) := by
  classical
  by_cases hNr : N ≤ r
  · apply (hcentral r hNr).trans
    apply fraction_mono
    intro y hy
    have hh := (mem_filter.mp hy).2
    have hs : Real.sqrt (r : ℝ) ≤ Real.sqrt (k : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hr)
    exact mem_filter.mpr ⟨mem_univ _, by constructor <;> linarith [hh.1, hh.2]⟩
  · have hNr' : r ≤ N := by omega
    have hNreal : (N : ℝ) ≤ Real.sqrt (k : ℝ) :=
      (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by
        have hh : ((N * N : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        simpa only [Nat.cast_mul, pow_two] using hh)
    have hall : central r (Real.sqrt (k : ℝ)) = univ := by
      apply Finset.eq_univ_of_forall
      intro y
      have hy := ones_le y
      have hyreal : (ones y : ℝ) ≤ r := by exact_mod_cast hy
      have hrN : (r : ℝ) ≤ N := by exact_mod_cast hNr'
      have hon : (0 : ℝ) ≤ ones y := by positivity
      have hs := score_eq y
      apply mem_filter.mpr
      constructor
      · exact mem_univ _
      · constructor <;> nlinarith [Real.sqrt_nonneg (k : ℝ)]
    rw [hall, fraction_univ_cube]
    exact ha

lemma conditional_tail_bounds {k r : ℕ} {p : ℝ} (hk : 4 ≤ k) (hr : r ≤ k)
    (hp : p ≤ fraction (tail (2 * k - r) 4 1))
    (hm : p ≤ fraction (tail (2 * k - r) 4 (-1)))
    (y : Fin r → Bool) (hy : y ∈ central r (Real.sqrt (k : ℝ))) :
    p ≤ fraction (univ.filter (fun u : Fin (2 * k - r) → Bool ↦
      k + ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ ones y + ones u)) ∧
    p ≤ fraction (univ.filter (fun u : Fin (2 * k - r) → Bool ↦
      ones y + ones u + ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ k)) := by
  classical
  have hyy := (mem_filter.mp hy).2
  have hn : k ≤ 2 * k - r := by omega
  have hnadd : r + (2 * k - r) = 2 * k := by omega
  have hnreal : (r : ℝ) + (2 * k - r : ℕ) = 2 * (k : ℝ) := by exact_mod_cast hnadd
  have hsqrt : Real.sqrt (k : ℝ) ≤ Real.sqrt (2 * k - r : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hd := ceil_half_le_sqrt k hk
  constructor
  · apply hm.trans
    apply fraction_mono
    intro u hu
    have htail := (mem_filter.mp hu).2
    simp only [neg_one_mul] at htail
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    have hh : (k : ℝ) + ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ (ones y : ℝ) + ones u := by
      nlinarith [score_eq y, score_eq u, hyy.2]
    exact_mod_cast hh
  · apply hp.trans
    apply fraction_mono
    intro u hu
    have htail := (mem_filter.mp hu).2
    simp only [one_mul] at htail
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    have hh : (ones y : ℝ) + ones u + ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ (k : ℝ) := by
      nlinarith [score_eq y, score_eq u, hyy.1]
    exact_mod_cast hh

noncomputable def good (k r : ℕ) (c : ℝ) : Finset (Fin r → Bool) :=
  by classical exact univ.filter (fun y ↦
    c ≤ fraction (univ.filter (fun u : Fin (2 * k - r) → Bool ↦
      k + ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ ones y + ones u)) ∧
    c ≤ fraction (univ.filter (fun u : Fin (2 * k - r) → Bool ↦
      ones y + ones u + ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ k)))

lemma good_mono {k r : ℕ} {a b : ℝ} (h : b ≤ a) : good k r a ⊆ good k r b := by
  classical
  intro y hy
  have hh := (mem_filter.mp hy).2
  exact mem_filter.mpr ⟨mem_univ _, h.trans hh.1, h.trans hh.2⟩

lemma shrink_constant {k r : ℕ} {a b : ℝ} (h : b ≤ a)
    (ha : a ≤ fraction (good k r a)) : b ≤ fraction (good k r b) :=
  h.trans (ha.trans (fraction_mono (good_mono h)))

lemma uniform_lemma11 :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ k r : ℕ, 2 ≤ k → r ≤ k →
      c ≤ fraction (good k r c) := by
  classical
  obtain ⟨a, p, ha, ha1, hp, N, hN, htail, hupper⟩ := eventual_tail_bounds
  let K : ℕ := max 4 (N * N + N)
  obtain ⟨c0, hc0, hc01, hfinite⟩ := bounded_lemma11 K
  let c : ℝ := min c0 (min a p)
  have hc0' : c ≤ c0 := min_le_left _ _
  have hca : c ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hcp : c ≤ p := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, lt_min hc0 (lt_min ha hp), hc0'.trans_lt hc01, ?_⟩
  intro k r hk hr
  by_cases hkK : k ≤ K
  · apply shrink_constant hc0'
    simpa only [good, fraction_cube] using hfinite k r hk hkK hr
  · have hKk : K ≤ k := by omega
    have hk4 : 4 ≤ k := (le_max_left _ _).trans hKk
    have hkN : N * N ≤ k := by have := (le_max_right 4 (N * N + N)).trans hKk; omega
    have hNk : N ≤ k := by have := (le_max_right 4 (N * N + N)).trans hKk; omega
    have hcentral : ∀ n : ℕ, N ≤ n → a ≤ fraction (central n (Real.sqrt (n : ℝ))) := by
      intro n hn
      exact central_fraction_ge (hupper n hn 1 (Or.inl rfl))
        (hupper n hn (-1) (Or.inr rfl))
    have hpref := central_large_capacity ha1.le hN hkN hr hcentral
    apply hca.trans (hpref.trans (fraction_mono ?_))
    intro y hy
    have hn : N ≤ 2 * k - r := by omega
    have hh := conditional_tail_bounds hk4 hr
      (htail _ hn 1 (Or.inl rfl)) (htail _ hn (-1) (Or.inr rfl)) y hy
    exact mem_filter.mpr ⟨mem_univ _, hcp.trans hh.1, hcp.trans hh.2⟩

end Lemma11Proof

theorem solution :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∀ k r : ℕ, 2 ≤ k → r ≤ k →
      c ≤ ((Finset.univ.filter (fun y : Fin r → Bool =>
            c ≤ ((Finset.univ.filter (fun u : Fin (2 * k - r) → Bool =>
                    k + ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤
                      (Finset.univ.filter (fun j => y j = true)).card +
                        (Finset.univ.filter (fun j => u j = true)).card)).card : ℝ) /
                  2 ^ (2 * k - r) ∧
            c ≤ ((Finset.univ.filter (fun u : Fin (2 * k - r) → Bool =>
                    (Finset.univ.filter (fun j => y j = true)).card +
                        (Finset.univ.filter (fun j => u j = true)).card +
                      ⌈Real.sqrt (k : ℝ) / 2⌉₊ ≤ k)).card : ℝ) /
                  2 ^ (2 * k - r))).card : ℝ) / 2 ^ r := by
  classical
  have h := Lemma11Proof.uniform_lemma11
  unfold Lemma11Proof.good at h
  simp only [Lemma11Proof.fraction_cube] at h
  unfold Lemma11Proof.ones at h
  exact h

