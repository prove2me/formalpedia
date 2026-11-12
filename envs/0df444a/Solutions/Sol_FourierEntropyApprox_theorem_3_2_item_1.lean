-- Prove2me | solution 1 for FourierEntropyApprox.theorem_3_2_item_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T23:04:06.412092+00:00
-- url     : https://prove2.me/submissions/f3e6e94e-4a1f-4dc2-9bb5-77f1e876b049

import Mathlib
import Definitions.Def_FourierEntropyApprox_IsBoolean
import Definitions.Def_FourierEntropyApprox_majCompose

section
set_option autoImplicit false
namespace FourierEntropyApprox.Dev.Item1
open FourierEntropyApprox

noncomputable def w (p : ℝ) (b : Bool) : ℝ := (1 + spin b * p) / 2

lemma prodw (t : ℕ) (p : ℝ) (y : Cube t) :
    ∏ i, w p (y i) = ((2:ℝ) ^ t)⁻¹ * ∑ S : Finset (Fin t), p ^ S.card * walsh S y := by
  have h1 : ∏ i, w p (y i) = ((2:ℝ) ^ t)⁻¹ * ∏ i, (1 + p * spin (y i)) := by
    unfold w
    rw [Finset.prod_div_distrib]
    simp [div_eq_inv_mul, mul_comm]
  rw [h1, Finset.prod_one_add, ← Finset.powerset_univ]
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, walsh]

lemma expand (t : ℕ) (p : ℝ) :
    ∑ S : Finset (Fin t), fourierCoeff (maj t) S * p ^ S.card
      = ∑ y : Cube t, (∏ i, w p (y i)) * maj t y := by
  simp only [prodw, fourierCoeff, avg, RCLike.ofReal_real_eq_id, id]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun S _ => ?_
  ring

lemma w_nonneg (p : ℝ) (hp : |p| ≤ 1) (b : Bool) : 0 ≤ w p b := by
  have := abs_le.mp hp
  unfold w spin; split_ifs <;> linarith

lemma sum_prod_eq (t : ℕ) (g : Bool → ℝ) :
    ∑ y : Cube t, ∏ i, g (y i) = (g true + g false) ^ t := by
  have := Finset.prod_univ_sum (fun _ : Fin t => (Finset.univ : Finset Bool)) (fun _ b => g b)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  simp [Finset.prod_const]

lemma sum_w (t : ℕ) (p : ℝ) : ∑ y : Cube t, ∏ i, w p (y i) = 1 := by
  rw [sum_prod_eq]
  have : w p true + w p false = 1 := by simp [w, spin]; ring
  rw [this, one_pow]

lemma cosh_ineq (d : ℝ) (hd : 0 ≤ d) :
    Real.cosh d - d * Real.sinh d ≤ Real.exp (-(d ^ 2) / 2) := by
  set g : ℝ → ℝ := fun d => Real.exp (-(d ^ 2) / 2) - Real.cosh d + d * Real.sinh d with hg
  have hder : ∀ x : ℝ, HasDerivAt g (x * (Real.cosh x - Real.exp (-(x ^ 2) / 2))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-x) x := by
      have := ((hasDerivAt_pow 2 x).neg).div_const 2
      exact this.congr_deriv (by norm_num; ring)
    have h2 := h1.exp
    have h3 := (Real.hasDerivAt_cosh x)
    have h4 := (hasDerivAt_id x).mul (Real.hasDerivAt_sinh x)
    have := (h2.sub h3).add h4
    exact this.congr_deriv (by simp; ring)
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x _ => (hder x).continuousAt.continuousWithinAt
    · exact fun x _ => (hder x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hder x).deriv]
      apply mul_nonneg (le_of_lt hx)
      have : Real.exp (-(x ^ 2) / 2) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      linarith [Real.one_le_cosh x]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hd) hd
  simp [hg] at this
  linarith

lemma key (t : ℕ) (p f δ : ℝ) (hp : |p| ≤ 1) (hf : f = 1 ∨ f = -1) (hδ : 0 < δ)
    (hfp : δ ≤ f * p) :
    |f - ∑ S : Finset (Fin t), fourierCoeff (maj t) S * p ^ S.card|
      ≤ 2 * Real.exp (-((t : ℝ) * δ ^ 2) / 2) := by
  rw [expand]
  have hQ := w_nonneg p hp
  have hsum : f = ∑ y : Cube t, (∏ i, w p (y i)) * f := by
    rw [← Finset.sum_mul, sum_w, one_mul]
  have hrw : f - ∑ y : Cube t, (∏ i, w p (y i)) * maj t y
      = ∑ y : Cube t, (∏ i, w p (y i)) * (f - maj t y) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, sum_w, one_mul]
  have hf2 : ∀ y : Cube t, |f - maj t y| ≤ 2 * ∏ i, Real.exp (-δ * (f * spin (y i))) := by
    intro y
    rw [← Real.exp_sum]
    have hpos := Real.exp_pos (∑ i, -δ * (f * spin (y i)))
    by_cases h : 0 ≤ ∑ i, spin (y i)
    · have hm : maj t y = 1 := by simp [maj, h]
      rcases hf with rfl | rfl
      · have e0 : |(1:ℝ) - 1| = 0 := by norm_num
        rw [hm, e0]; positivity
      · have : 0 ≤ ∑ i, -δ * ((-1) * spin (y i)) := by
          rw [← Finset.mul_sum]
          have : ∑ i, (-1 : ℝ) * spin (y i) = -∑ i, spin (y i) := by simp
          rw [this]; nlinarith
        have h1 := Real.one_le_exp this
        have e0 : |(-1:ℝ) - 1| = 2 := by norm_num
        rw [hm, e0]; linarith
    · push Not at h
      have hm : maj t y = -1 := by simp [maj, not_le.mpr h]
      rcases hf with rfl | rfl
      · have : 0 ≤ ∑ i, -δ * (1 * spin (y i)) := by
          rw [← Finset.mul_sum]
          have : ∑ i, (1 : ℝ) * spin (y i) = ∑ i, spin (y i) := by simp
          rw [this]; nlinarith
        have h1 := Real.one_le_exp this
        have e0 : |(1:ℝ) - -1| = 2 := by norm_num
        rw [hm, e0]; linarith
      · have e0 : |(-1:ℝ) - -1| = 0 := by norm_num
        rw [hm, e0]; positivity
  calc |f - ∑ y : Cube t, (∏ i, w p (y i)) * maj t y|
      = |∑ y : Cube t, (∏ i, w p (y i)) * (f - maj t y)| := by rw [hrw]
    _ ≤ ∑ y : Cube t, |(∏ i, w p (y i)) * (f - maj t y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y : Cube t, (∏ i, w p (y i)) * (2 * ∏ i, Real.exp (-δ * (f * spin (y i)))) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun i _ => hQ _)]
        exact mul_le_mul_of_nonneg_left (hf2 y) (Finset.prod_nonneg fun i _ => hQ _)
    _ = 2 * ∑ y : Cube t, ∏ i, (w p (y i) * Real.exp (-δ * (f * spin (y i)))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ = 2 * (w p true * Real.exp (-δ * (f * spin true))
          + w p false * Real.exp (-δ * (f * spin false))) ^ t := by
        have := sum_prod_eq t (fun b => w p b * Real.exp (-δ * (f * spin b)))
        rw [this]
    _ ≤ 2 * Real.exp (-((t : ℝ) * δ ^ 2) / 2) := by
        have hb : w p true * Real.exp (-δ * (f * spin true))
            + w p false * Real.exp (-δ * (f * spin false)) ≤ Real.exp (-(δ ^ 2) / 2) := by
          have hc := cosh_ineq δ hδ.le
          have e : w p true * Real.exp (-δ * (f * spin true))
              + w p false * Real.exp (-δ * (f * spin false))
              = Real.cosh δ - (f * p) * Real.sinh δ := by
            rcases hf with rfl | rfl <;>
            · simp only [w, spin, if_true, Real.cosh_eq, Real.sinh_eq]
              simp only [Bool.false_eq_true, if_false]
              try ring_nf
              try simp [Real.exp_neg]
              try ring
          rw [e]
          have hs : 0 ≤ Real.sinh δ := Real.sinh_nonneg_iff.mpr hδ.le
          nlinarith
        have h0 : 0 ≤ w p true * Real.exp (-δ * (f * spin true))
            + w p false * Real.exp (-δ * (f * spin false)) := by
          have := hQ true; have := hQ false
          positivity
        have := pow_le_pow_left₀ h0 hb t
        have e2 : Real.exp (-(δ ^ 2) / 2) ^ t = Real.exp (-((t : ℝ) * δ ^ 2) / 2) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
        rw [e2] at this
        linarith

end FourierEntropyApprox.Dev.Item1

namespace FourierEntropyApprox
open FourierEntropyApprox.Dev.Item1 in
theorem chk_theorem_3_2_item_1 {n : ℕ} (f P : Cube n → ℝ) (δ : ℝ) (hf : IsBoolean f) (hδ : 0 < δ)
    (hP : ∀ x, |P x| ≤ 1) (hfP : ∀ x, δ ≤ f x * P x) (t : ℕ) :
    (∀ x, |f x - majCompose t P x| ≤ 2 * Real.exp (-((t : ℝ) * δ ^ 2) / 2)) ∧
      l2NormSq (f - majCompose t P) ≤ 4 * Real.exp (-((t : ℝ) * δ ^ 2)) := by
  have h1 : ∀ x, |f x - majCompose t P x| ≤ 2 * Real.exp (-((t : ℝ) * δ ^ 2) / 2) :=
    fun x => key t (P x) (f x) δ (hP x) (hf x) hδ (hfP x)
  refine ⟨h1, ?_⟩
  set E := Real.exp (-((t : ℝ) * δ ^ 2) / 2) with hE
  have hE2 : E ^ 2 = Real.exp (-((t : ℝ) * δ ^ 2)) := by
    rw [hE, ← Real.exp_nat_mul]; congr 1; ring
  unfold l2NormSq
  have hsum : ∑ x, ‖(f - majCompose t P) x‖ ^ 2 ≤ ∑ _x : Cube n, (2 * E) ^ 2 := by
    refine Finset.sum_le_sum fun x _ => ?_
    have := h1 x
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hpos : 0 ≤ ((2:ℝ) ^ n)⁻¹ := by positivity
  calc ((2:ℝ) ^ n)⁻¹ * ∑ x, ‖(f - majCompose t P) x‖ ^ 2
      ≤ ((2:ℝ) ^ n)⁻¹ * ∑ _x : Cube n, (2 * E) ^ 2 := mul_le_mul_of_nonneg_left hsum hpos
    _ = 4 * Real.exp (-((t : ℝ) * δ ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ]
        simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [← hE2]
        field_simp
        ring
end FourierEntropyApprox
end

theorem solution : type_of% @FourierEntropyApprox.chk_theorem_3_2_item_1 := @FourierEntropyApprox.chk_theorem_3_2_item_1
