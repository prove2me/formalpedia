-- Prove2me | solution 1 for FourierEntropyApprox.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:04:08.023827+00:00
-- url     : https://prove2.me/submissions/c1bc0dd5-80bb-4a08-b2d6-b66e2ed35cbb

import Mathlib
import Definitions.Def_FourierEntropyApprox_approxSpectralNorm
import Definitions.Def_FourierEntropyApprox_entropyFun
import Definitions.Def_FourierEntropyApprox_IsBoolean
import Definitions.Def_FourierEntropyApprox_majCompose
import Definitions.Def_FourierEntropyApprox_Ka
import Theorems.Thm_FourierEntropyApprox_theorem_3_1
import Theorems.Thm_FourierEntropyApprox_theorem_3_2_Qj
import Theorems.Thm_FourierEntropyApprox_theorem_3_2_item_1
import Theorems.Thm_FourierEntropyApprox_theorem_3_2_item_2

section
set_option autoImplicit false

namespace FourierEntropyApprox.Dev.Thm32
open FourierEntropyApprox

lemma fc_cast {n : ℕ} (g : Cube n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun x => ((g x : ℝ) : ℂ)) S = ((fourierCoeff g S : ℝ) : ℂ) := by
  simp [fourierCoeff, avg]

lemma sn_cast {n : ℕ} (g : Cube n → ℝ) :
    spectralNorm (fun x => ((g x : ℝ) : ℂ)) = spectralNorm g := by
  simp [spectralNorm, fc_cast]

lemma ent_cast {n : ℕ} (g : Cube n → ℝ) :
    entropyFun (fun x => ((g x : ℝ) : ℂ)) = entropyFun g := by
  simp [entropyFun, fc_cast]

lemma l2_cast_sub {n : ℕ} (f Q : Cube n → ℝ) :
    l2NormSq ((fun x => ((f x : ℝ) : ℂ)) - fun x => ((Q x : ℝ) : ℂ)) = l2NormSq (f - Q) := by
  simp [l2NormSq, ← Complex.ofReal_sub, sq_abs]

lemma fc_smul {n : ℕ} (c : ℝ) (p : Cube n → ℝ) (S : Finset (Fin n)) :
    fourierCoeff (fun x => c * p x) S = c * fourierCoeff p S := by
  simp only [fourierCoeff, avg]
  rw [Finset.mul_sum, Finset.mul_sum]
  simp only [mul_assoc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma sn_smul {n : ℕ} (c : ℝ) (p : Cube n → ℝ) :
    spectralNorm (fun x => c * p x) = |c| * spectralNorm p := by
  simp only [spectralNorm, fc_smul, norm_mul, Real.norm_eq_abs]
  rw [Finset.mul_sum]

lemma sn_nonneg {n : ℕ} (p : Cube n → ℝ) : 0 ≤ spectralNorm p :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

lemma walsh_orth {n : ℕ} (x y : Cube n) :
    ∑ S : Finset (Fin n), walsh S x * walsh S y = if y = x then (2 : ℝ) ^ n else 0 := by
  have h1 : ∀ S : Finset (Fin n), walsh S x * walsh S y
      = ∏ i ∈ S, (spin (x i) * spin (y i)) := by
    intro S
    simp only [walsh, Finset.prod_mul_distrib]
  simp only [h1]
  have h2 : ∑ S : Finset (Fin n), ∏ i ∈ S, (spin (x i) * spin (y i))
      = ∏ i : Fin n, (1 + spin (x i) * spin (y i)) := by
    rw [Finset.prod_one_add, Finset.powerset_univ]
  rw [h2]
  split_ifs with h
  · subst h
    have : ∀ i : Fin n, 1 + spin (y i) * spin (y i) = 2 := by
      intro i; unfold spin; split_ifs <;> norm_num
    simp [this]
  · have : ∃ i, y i ≠ x i := by
      by_contra hh; push Not at hh; exact h (funext hh)
    obtain ⟨i, hi⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    unfold spin
    cases hx : x i <;> cases hy : y i <;> simp_all

lemma inversion {n : ℕ} (p : Cube n → ℝ) (x : Cube n) :
    p x = ∑ S : Finset (Fin n), fourierCoeff p S * walsh S x := by
  have h : ∀ S : Finset (Fin n), fourierCoeff p S * walsh S x
      = ((2 : ℝ) ^ n)⁻¹ * ∑ y, p y * (walsh S y * walsh S x) := by
    intro S
    simp only [fourierCoeff, avg]
    simp only [RCLike.ofReal_real_eq_id, id]
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    ring
  simp only [h]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum, walsh_orth]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

lemma abs_walsh {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : |walsh S x| = 1 := by
  unfold walsh
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro i _
  unfold spin; split_ifs <;> simp

lemma abs_le_sn {n : ℕ} (p : Cube n → ℝ) (x : Cube n) : |p x| ≤ spectralNorm p := by
  conv_lhs => rw [inversion p x]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro S _
  rw [abs_mul, abs_walsh, mul_one]
  simp

end FourierEntropyApprox.Dev.Thm32

namespace FourierEntropyApprox
open FourierEntropyApprox.Dev.Thm32 in
theorem chk_theorem_3_2 :
    ∀ ε : ℝ, 0 ≤ ε → ε < 1 → ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (f : Cube n → ℝ), IsBoolean f →
      entropyFun f ≤ K * Real.logb 2 (1 + approxSpectralNorm ε f) := by
  intro ε hε0 hε1
  have hδpos : 0 < (1 - ε) / (1 + ε) := div_pos (by linarith) (by linarith)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, 2 * Real.exp (-((t : ℝ) * ((1 - ε) / (1 + ε)) ^ 2) / 2) ≤ 1 / 3 := by
    set δ := (1 - ε) / (1 + ε) with hδ
    have hδ2 : 0 < δ ^ 2 := by positivity
    refine ⟨⌈2 * Real.log 6 / δ ^ 2⌉₊, ?_⟩
    have h1 : 2 * Real.log 6 / δ ^ 2 ≤ (⌈2 * Real.log 6 / δ ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : 2 * Real.log 6 ≤ (⌈2 * Real.log 6 / δ ^ 2⌉₊ : ℝ) * δ ^ 2 := by
      rwa [div_le_iff₀ hδ2] at h1
    have h3 : Real.exp (-((⌈2 * Real.log 6 / δ ^ 2⌉₊ : ℝ) * δ ^ 2) / 2) ≤ Real.exp (-Real.log 6) := by
      apply Real.exp_le_exp.mpr; linarith
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at h3
    linarith
  obtain ⟨c, hc, hQ⟩ := theorem_3_2_Qj
  have hKa : 0 ≤ Ka 1 := by
    unfold Ka KaTerm
    apply tsum_nonneg
    intro j; positivity
  set m := Real.logb 2 (2 - ε) with hmdef
  have hm : 0 < m := Real.logb_pos (by norm_num) (by linarith)
  set K1 : ℝ := ((t : ℝ) + 1) * (1 / m + 1) with hK1
  refine ⟨6 / m + 4 * c * Ka 1 * K1, by positivity, ?_⟩
  intro n f hf
  have hfabs : ∀ x, |f x| = 1 := fun x => by rcases hf x with h | h <;> simp [h]
  set S0 : Set ℝ := {s | ∃ p : Cube n → ℝ, (∀ x, |p x - f x| ≤ ε) ∧ spectralNorm p = s} with hS0
  have hne : S0.Nonempty := ⟨spectralNorm f, f, fun x => by simp [hε0], rfl⟩
  have hlow : ∀ s ∈ S0, 1 - ε ≤ s := by
    rintro s ⟨p, hp, rfl⟩
    let x0 : Cube n := fun _ => false
    have h0 := abs_le_sn p x0
    have h1 := abs_le.mp (hp x0)
    have h3 := le_abs_self (p x0)
    have h4 := neg_le_abs (p x0)
    rcases hf x0 with h | h <;> rw [h] at h1 <;> linarith [h1.1, h1.2]
  have hs : 1 - ε ≤ approxSpectralNorm ε f := le_csInf hne hlow
  set s := approxSpectralNorm ε f with hsdef
  have hs0 : 0 < s := by linarith
  obtain ⟨b, ⟨p, hp, rfl⟩, hb⟩ := exists_lt_of_csInf_lt hne (show sInf S0 < 2 * s by
    show s < 2 * s; linarith)
  have hpx : ∀ x, |p x| ≤ 1 + ε := fun x => by
    have := abs_le.mp (hp x)
    rw [abs_le]; rcases hf x with h | h <;> rw [h] at this <;> constructor <;> linarith [this.1, this.2]
  have hfp : ∀ x, 1 - ε ≤ f x * p x := fun x => by
    have := abs_le.mp (hp x)
    rcases hf x with h | h <;> rw [h] at this ⊢ <;> linarith [this.1, this.2]
  have hε1p : 0 < 1 + ε := by linarith
  set P0 : Cube n → ℝ := fun x => (1 + ε)⁻¹ * p x with hP0
  have hP0b : ∀ x, |P0 x| ≤ 1 := fun x => by
    simp only [hP0]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hε1p), inv_mul_le_iff₀ hε1p]
    linarith [hpx x]
  have hfP0 : ∀ x, (1 - ε) / (1 + ε) ≤ f x * P0 x := fun x => by
    simp only [hP0]
    have : f x * ((1 + ε)⁻¹ * p x) = (1 + ε)⁻¹ * (f x * p x) := by ring
    rw [this, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hfp x) (inv_nonneg.mpr hε1p.le)
  obtain ⟨h1, -⟩ := theorem_3_2_item_1 f P0 _ hf hδpos hP0b hfP0 t
  have hP'' : ∀ x, |majCompose t P0 x - f x| ≤ 1 / 3 := fun x => by
    rw [abs_sub_comm]; exact (h1 x).trans ht
  obtain hQ' := hQ n f (majCompose t P0) hf hP''
  set P'' := majCompose t P0 with hP''def
  set B := spectralNorm (fun x => 3 * P'' x / 4) with hB
  have hBeq : B = 3 / 4 * spectralNorm P'' := by
    have : (fun x => 3 * P'' x / 4) = fun x => (3 / 4 : ℝ) * P'' x := by
      funext x; ring
    rw [hB, this, sn_smul, abs_of_pos (by norm_num)]
  have hB0 : spectralNorm P0 ≤ 2 * s := by
    have : spectralNorm P0 = (1 + ε)⁻¹ * spectralNorm p := by
      rw [hP0, sn_smul, abs_of_pos (inv_pos.mpr hε1p)]
    rw [this]
    have h5 : (1 + ε)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have := sn_nonneg p
    nlinarith
  have hB0n := sn_nonneg P0
  have hP''n := sn_nonneg P''
  have h2 := theorem_3_2_item_2 P0 t
  set y := 1 + s with hy
  have hy1 : 1 ≤ y := by linarith
  have hBb : B ≤ (2 * y) ^ t := by
    have e1 : 1 + spectralNorm P0 ^ 2 ≤ (2 * y) ^ 2 := by nlinarith
    have e2 : (1 + spectralNorm P0 ^ 2) ^ ((t : ℝ) / 2) ≤ ((2 * y) ^ 2) ^ ((t : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) e1 (by positivity)
    have e3 : ((2 * y) ^ 2) ^ ((t : ℝ) / 2) = (2 * y) ^ t := by
      rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
      rw [show (2 : ℝ) * ((t : ℝ) / 2) = (t : ℝ) by ring, Real.rpow_natCast]
    rw [hBeq]
    have : (0 : ℝ) ≤ (2 * y) ^ t := by positivity
    linarith
  have hz1 : (1 : ℝ) ≤ (2 * y) ^ t := one_le_pow₀ (by linarith)
  have hB1 : 1 + B ≤ (2 * y) ^ (t + 1) := by
    rw [pow_succ]
    nlinarith [hBeq, sn_nonneg P'']
  have hBpos : 0 < 1 + B := by rw [hBeq]; linarith
  have hlogB : Real.logb 2 (1 + B) ≤ ((t : ℝ) + 1) * (1 + Real.logb 2 y) := by
    calc Real.logb 2 (1 + B) ≤ Real.logb 2 ((2 * y) ^ (t + 1)) :=
          Real.logb_le_logb_of_le (by norm_num) hBpos hB1
      _ = ((t : ℝ) + 1) * (1 + Real.logb 2 y) := by
          rw [Real.logb_pow, Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)]
          push_cast; ring
  set Y := Real.logb 2 y with hYdef
  have hmY : m ≤ Y := Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hY0 : 0 ≤ Y := hm.le.trans hmY
  have hr : 1 ≤ Y / m := by rw [le_div_iff₀ hm]; linarith
  have hLb : max 1 (Real.logb 2 (1 + B)) ≤ K1 * Y := by
    have e : K1 * Y = ((t : ℝ) + 1) * (Y / m + Y) := by rw [hK1]; field_simp
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    apply max_le
    · rw [e]; nlinarith
    · rw [e]; nlinarith
  -- apply Theorem 3.1
  have hL1 : (1 : ℝ) ≤ max 1 (Real.logb 2 (1 + B)) := le_max_left _ _
  have hf2 : l2NormSq (fun x => ((f x : ℝ) : ℂ)) ≤ 1 := by
    have : ∀ x, ‖((f x : ℝ) : ℂ)‖ ^ 2 = 1 := fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs, hfabs]; norm_num
    simp only [l2NormSq, this]
    simp
  have h31 := theorem_3_1 (fun x => ((f x : ℝ) : ℂ)) 1 c (max 1 (Real.logb 2 (1 + B)))
    (fun j x => ((majCompose (4 * j + 8) (fun x => 3 * P'' x / 4) x : ℝ) : ℂ))
    hf2 zero_le_one hc hL1 (by
      intro j hj
      obtain ⟨hq1, hq2⟩ := hQ' j hj
      refine ⟨by rw [l2_cast_sub]; exact hq1, ?_⟩
      rw [sn_cast, Real.rpow_one]
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hlb : Real.logb 2 (1 + B) ≤ max 1 (Real.logb 2 (1 + B)) := le_max_right _ _
      have : c * j * Real.logb 2 (1 + B) ≤ c * j * max 1 (Real.logb 2 (1 + B)) :=
        mul_le_mul_of_nonneg_left hlb (by positivity)
      nlinarith [mul_pos hc (show (0:ℝ) < max 1 (Real.logb 2 (1 + B)) by linarith)])
  rw [ent_cast] at h31
  have h6 : 6 ≤ 6 / m * Y := by
    have : 6 / m * Y = 6 * (Y / m) := by ring
    rw [this]; linarith
  have hnn : 0 ≤ 4 * c * Ka 1 := by positivity
  have := mul_le_mul_of_nonneg_left hLb hnn
  have e : (6 / m + 4 * c * Ka 1 * K1) * Y = 6 / m * Y + 4 * c * Ka 1 * (K1 * Y) := by ring
  rw [e]
  have e2 : 4 * c * Ka 1 * max 1 (Real.logb 2 (1 + B)) ≤ 4 * c * Ka 1 * (K1 * Y) := this
  have e3 : 6 + 4 * c * Ka 1 * max 1 (Real.logb 2 (1 + B)) ≤ 6 + 4 * c * Ka 1 * (K1 * Y) := by
    linarith
  have e4 : 4 * c * Ka 1 * max 1 (Real.logb 2 (1 + B)) = 4 * c * Ka 1 * max 1 (Real.logb 2 (1 + B)) := rfl
  linarith
end FourierEntropyApprox
end

theorem solution : type_of% @FourierEntropyApprox.chk_theorem_3_2 := @FourierEntropyApprox.chk_theorem_3_2
