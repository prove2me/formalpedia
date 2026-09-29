-- Prove2me | solution 1 for Gelbart.hecke_nice_of_automorphic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:28:52.509381+00:00
-- url     : https://prove2.me/submissions/bae146bd-0ce5-476b-86da-d932d69ee07d

import Mathlib
import Definitions.Def_Gelbart_hecke_conditions

open Complex Real Filter Topology Set MeasureTheory Asymptotics

namespace Gelbart

/-- the summands of `heckeForm` on the imaginary axis -/
noncomputable def hterm (a : ℕ → ℂ) (h : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  a n * ((Real.exp (-(2 * π * n / h) * x) : ℝ) : ℂ)

lemma heckeForm_I_mul (a : ℕ → ℂ) (h x : ℝ) :
    heckeForm a h (I * x) = ∑' n, hterm a h n x := by
  unfold heckeForm hterm
  congr 1
  funext n
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- polynomial bound on the coefficients valid for every index -/
lemma coeff_bound (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c) (hgrowth : HeckeCoeffGrowth a c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ m : ℕ, ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + ‖a 0‖ := by
  obtain ⟨K, hK⟩ := hgrowth
  refine ⟨max K 0, le_max_right _ _, Nat.ceil c, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (0 : ℝ) ≤ max K 0 * ((0 : ℕ) : ℝ) ^ Nat.ceil c := by
      apply mul_nonneg (le_max_right _ _); positivity
    linarith
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 := hK n hn
    have h2 : (n : ℝ) ^ c ≤ (n : ℝ) ^ (Nat.ceil c : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (Nat.le_ceil c)
    rw [Real.rpow_natCast] at h2
    have h3 : K * (n : ℝ) ^ c ≤ max K 0 * (n : ℝ) ^ Nat.ceil c := by
      calc K * (n : ℝ) ^ c ≤ max K 0 * (n : ℝ) ^ c := by
            apply mul_le_mul_of_nonneg_right (le_max_left _ _); positivity
        _ ≤ max K 0 * (n : ℝ) ^ Nat.ceil c := by
            apply mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    have := norm_nonneg (a 0)
    linarith

lemma summable_bound (K A : ℝ) (m : ℕ) {α : ℝ} (hα : 0 < α) :
    Summable (fun n : ℕ => (K * (n : ℝ) ^ m + A) * Real.exp (-(α * n))) := by
  have hr : ‖Real.exp (-α)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.2 (by linarith)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one m hr
  have h2 := summable_geometric_of_norm_lt_one hr
  have h3 := (h1.mul_left K).add (h2.mul_left A)
  refine h3.congr fun n => ?_
  rw [← Real.exp_nat_mul]
  ring_nf

/-- the Hecke form on the imaginary axis -/
noncomputable def phi (a : ℕ → ℂ) (h : ℝ) (x : ℝ) : ℂ := heckeForm a h (I * x)

lemma norm_hterm (a : ℕ → ℂ) (h : ℝ) (n : ℕ) (x : ℝ) :
    ‖hterm a h n x‖ = ‖a n‖ * Real.exp (-(2 * π * n / h) * x) := by
  unfold hterm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma hterm_le (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) {δ x : ℝ} (hδ : δ ≤ x) (n : ℕ) :
    ‖hterm a h n x‖ ≤ (K * (n : ℝ) ^ m + A) * Real.exp (-((2 * π * δ / h) * n)) := by
  rw [norm_hterm]
  apply mul_le_mul (hK n) _ (Real.exp_pos _).le ((norm_nonneg _).trans (hK n))
  apply Real.exp_le_exp.2
  have : 0 ≤ 2 * π * n / h := by positivity
  have : (2 * π * δ / h) * n = (2 * π * n / h) * δ := by ring
  nlinarith

lemma phi_eq_tsum (a : ℕ → ℂ) (h x : ℝ) : phi a h x = ∑' n, hterm a h n x :=
  heckeForm_I_mul a h x

lemma summable_hterm (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) {x : ℝ} (hx : 0 < x) :
    Summable (fun n => hterm a h n x) := by
  apply Summable.of_norm_bounded (summable_bound K A m (by positivity : 0 < 2 * π * x / h))
  intro n
  exact hterm_le a h hh K A m hK (le_refl x) n

lemma continuousOn_phi (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) : ContinuousOn (phi a h) (Ioi 0) := by
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  have hcont : ContinuousOn (fun y => ∑' n, hterm a h n y) (Ici (x / 2)) := by
    apply continuousOn_tsum (u := fun n : ℕ => (K * (n : ℝ) ^ m + A) *
      Real.exp (-((2 * π * (x / 2) / h) * n)))
    · intro n
      unfold hterm
      fun_prop
    · exact summable_bound K A m (by positivity)
    · intro n y hy
      exact hterm_le a h hh K A m hK hy n
  have : ContinuousAt (fun y => ∑' n, hterm a h n y) x :=
    hcont.continuousAt (Ici_mem_nhds (by linarith))
  have heq : phi a h = fun y => ∑' n, hterm a h n y := funext (phi_eq_tsum a h)
  rw [heq]
  exact this.continuousWithinAt

lemma phi_sub_bound (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) :
    ∃ S : ℝ, ∀ x : ℝ, 1 ≤ x → ‖phi a h x - a 0‖ ≤ S * Real.exp (-(2 * π / h) * (x - 1)) := by
  set β := 2 * π / h with hβ
  have hβ0 : 0 < β := by positivity
  set u : ℕ → ℝ := fun n => (K * ((n + 1 : ℕ) : ℝ) ^ m + A) * Real.exp (-(β * (n + 1 : ℕ)))
  have hu : Summable u := by
    have := summable_bound K A m hβ0
    exact (summable_nat_add_iff 1).2 this
  refine ⟨∑' n, u n, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hs := summable_hterm a h hh K A m hK hx0
  rw [phi_eq_tsum, hs.tsum_eq_zero_add]
  have h0 : hterm a h 0 x = a 0 := by simp [hterm]
  rw [h0, add_sub_cancel_left]
  have hs' : Summable (fun n => hterm a h (n + 1) x) := (summable_nat_add_iff 1).2 hs
  have hb : ∀ n : ℕ, ‖hterm a h (n + 1) x‖ ≤ u n * Real.exp (-β * (x - 1)) := by
    intro n
    rw [norm_hterm]
    simp only [u]
    refine le_trans ?_ (le_of_eq (mul_assoc _ _ _).symm)
    apply mul_le_mul ((hK (n + 1))) _ (Real.exp_pos _).le
      ((norm_nonneg _).trans (hK (n + 1)))
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have : -(2 * π * ((n + 1 : ℕ) : ℝ) / h) * x = -(β * ((n + 1 : ℕ) : ℝ)) * x := by
      rw [hβ]; ring
    rw [this]
    push_cast
    nlinarith [mul_nonneg (mul_nonneg hβ0.le (Nat.cast_nonneg n)) (sub_nonneg.2 hx)]
  calc ‖∑' n, hterm a h (n + 1) x‖ ≤ ∑' n, u n * Real.exp (-β * (x - 1)) :=
        tsum_of_norm_bounded (hu.mul_right _).hasSum hb
    _ = (∑' n, u n) * Real.exp (-β * (x - 1)) := tsum_mul_right

lemma phi_isBigO (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) (r : ℝ) :
    (fun x => phi a h x - a 0) =O[atTop] (fun x : ℝ => x ^ r) := by
  obtain ⟨S, hS⟩ := phi_sub_bound a h hh K A m hK
  have hβ0 : 0 < 2 * π / h := by positivity
  have h1 : (fun x => phi a h x - a 0) =O[atTop] (fun x => Real.exp (-(2 * π / h) * x)) := by
    apply IsBigO.of_bound (|S| * Real.exp (2 * π / h))
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc ‖phi a h x - a 0‖ ≤ S * Real.exp (-(2 * π / h) * (x - 1)) := hS x hx
      _ ≤ |S| * Real.exp (-(2 * π / h) * (x - 1)) := by
          gcongr; exact le_abs_self S
      _ = |S| * Real.exp (2 * π / h) * Real.exp (-(2 * π / h) * x) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop hβ0 r).isBigO

lemma phi_feq (a : ℕ → ℂ) (h k : ℝ) (C : ℂ) (hA : HeckeAutomorphic a h k C) {x : ℝ}
    (hx : 0 < x) : phi a h (1 / x) = (C * ↑(x ^ k)) • phi a h x := by
  have hz : 0 < (I * (x : ℂ)).im := by simp [hx]
  have := hA (I * x) hz
  unfold phi
  have e1 : (-1 / (I * (x : ℂ))) = I * ((1 / x : ℝ) : ℂ) := by
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast
    field_simp
    rw [Complex.I_sq]
  have e2 : (I * (x : ℂ) / I) ^ (k : ℂ) = ((x ^ k : ℝ) : ℂ) := by
    rw [mul_div_cancel_left₀ _ Complex.I_ne_zero, Complex.ofReal_cpow hx.le]
  rw [← e1, this, e2, smul_eq_mul]

/-- coefficients with the constant term removed -/
noncomputable def aa (a : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else a n

/-- frequencies -/
noncomputable def pp (h : ℝ) (n : ℕ) : ℝ := 2 * π * n / h

lemma hasSum_phi_sub (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n => aa a n * (Real.exp (-pp h n * t) : ℂ)) (phi a h t - a 0) := by
  have hs := (summable_hterm a h hh K A m hK ht).hasSum
  rw [← phi_eq_tsum] at hs
  have h2 := hs.sub (hasSum_ite_eq 0 (a 0))
  have e : (fun n => aa a n * (Real.exp (-pp h n * t) : ℂ))
      = (fun b => hterm a h b t - if b = 0 then a 0 else 0) := by
    funext n
    unfold aa hterm pp
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [hn.ne']
  rw [e]; exact h2

lemma summable_aa_div (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : HeckeCoeffGrowth a c) {σ : ℝ} (hσ : c + 1 < σ) :
    Summable (fun n => ‖aa a n‖ / (pp h n) ^ σ) := by
  obtain ⟨K, hK⟩ := hgrowth
  have hσ0 : 0 < σ := by linarith
  set B := |K| * (h / (2 * π)) ^ σ
  have hs : Summable (fun n : ℕ => B * (n : ℝ) ^ (c - σ)) :=
    (Real.summable_nat_rpow.2 (by linarith)).mul_left B
  refine Summable.of_nonneg_of_le
    (fun n => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (by unfold pp; positivity) _))
    (fun n => ?_) hs
  unfold aa pp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
    exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _)
  · simp only [hn.ne', if_false]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hp : (2 * π * n / h) ^ σ = (2 * π / h) ^ σ * (n : ℝ) ^ σ := by
      rw [← Real.mul_rpow (by positivity) hn0.le]; ring_nf
    rw [hp, div_le_iff₀ (by positivity)]
    calc ‖a n‖ ≤ K * (n : ℝ) ^ c := hK n hn
      _ ≤ |K| * (n : ℝ) ^ c := by gcongr; exact le_abs_self K
      _ = B * (n : ℝ) ^ (c - σ) * ((2 * π / h) ^ σ * (n : ℝ) ^ σ) := by
          simp only [B]
          rw [Real.rpow_sub hn0]
          have h1 : (h / (2 * π)) ^ σ * (2 * π / h) ^ σ = 1 := by
            rw [← Real.mul_rpow (by positivity) (by positivity)]
            rw [show h / (2 * π) * (2 * π / h) = 1 by field_simp]
            simp
          have h2 : (n : ℝ) ^ σ ≠ 0 := by positivity
          field_simp
          rw [mul_assoc, h1, mul_one]

lemma mellin_phi_sub (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : HeckeCoeffGrowth a c) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) {s : ℂ} (hs : c + 1 < s.re) :
    HasSum (fun i => Gamma s * aa a i / (pp h i : ℂ) ^ s) (mellin (fun t => phi a h t - a 0) s)
    ∧ mellin (fun t => phi a h t - a 0) s = heckeCompletedLSeries a h s := by
  have hp : ∀ i, aa a i = 0 ∨ 0 < pp h i := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · left; simp [aa]
    · right; unfold pp; have : (0:ℝ) < i := by exact_mod_cast hi
      positivity
  have hs0 : 0 < s.re := by linarith
  have hsum := hasSum_mellin (a := aa a) (p := pp h) (F := fun t => phi a h t - a 0) hp hs0
    (fun t ht => hasSum_phi_sub a h hh K A m hK ht) (summable_aa_div a c h hc hh hgrowth hs)
  refine ⟨hsum, ?_⟩
  rw [← hsum.tsum_eq]
  unfold heckeCompletedLSeries LSeries
  rw [← tsum_mul_left]
  congr 1
  funext i
  unfold aa pp LSeries.term
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · simp only [hi.ne', if_false]
    have hi0 : (0:ℝ) < i := by exact_mod_cast hi
    have e1 : ((2 * π * (i : ℝ) / h : ℝ) : ℂ) = ((2 * π / h : ℝ) : ℂ) * ((i : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, Complex.mul_cpow_ofReal_nonneg (by positivity) hi0.le, Complex.cpow_neg]
    have e2 : ((2 * π / h : ℝ) : ℂ) = 2 * (π : ℂ) / (h : ℂ) := by push_cast; ring
    rw [e2]
    have hne1 : (2 * (π : ℂ) / (h : ℂ)) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not
      intro h0
      exfalso
      have : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have : 2 * (π : ℂ) / (h : ℂ) ≠ 0 := by
        apply div_ne_zero (mul_ne_zero two_ne_zero ‹_›) ‹_›
      exact this h0
    have hne2 : ((i : ℝ) : ℂ) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; push Not
      intro h0; exfalso; exact (by exact_mod_cast hi0.ne' : ((i : ℝ) : ℂ) ≠ 0) h0
    push_cast at hne2 ⊢
    field_simp

lemma integral_term_norm (a : ℕ → ℂ) (h : ℝ) (hh : 0 < h) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    IntegrableOn (fun t : ℝ => ‖aa a n‖ * (t ^ (σ - 1) * Real.exp (-(pp h n * t)))) (Ioi 0) ∧
    ∫ t in Ioi 0, ‖aa a n‖ * (t ^ (σ - 1) * Real.exp (-(pp h n * t)))
      = Real.Gamma σ * (‖aa a n‖ / (pp h n) ^ σ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aa]
  · have hp : 0 < pp h n := by
      unfold pp; have : (0:ℝ) < n := by exact_mod_cast hn
      positivity
    have hint : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-(pp h n * t))) (Ioi 0) := by
      have := Real.GammaIntegral_convergent hσ
      rw [← mul_zero (pp h n), ← integrableOn_Ioi_comp_mul_left_iff _ _ hp] at this
      refine IntegrableOn.congr_fun (this.const_mul (1 / (pp h n) ^ (σ - 1)))
        (fun t ht => ?_) measurableSet_Ioi
      have ht' : (0:ℝ) < t := ht
      rw [Real.mul_rpow hp.le ht'.le]
      have : (pp h n) ^ (σ - 1) ≠ 0 := by positivity
      field_simp
    refine ⟨hint.const_mul _, ?_⟩
    rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hp]
    rw [Real.div_rpow zero_le_one hp.le, Real.one_rpow]
    ring

lemma mellinConvergent_phi_sub (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : HeckeCoeffGrowth a c) (K A : ℝ) (m : ℕ)
    (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) {σ : ℝ} (hσ : c + 1 < σ) :
    MellinConvergent (fun t => phi a h t - a 0) (σ : ℂ) := by
  have hσ0 : 0 < σ := by linarith
  set g : ℕ → ℝ → ℝ := fun n t => ‖aa a n‖ * (t ^ (σ - 1) * Real.exp (-(pp h n * t))) with hg
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1) • (phi a h t - a 0))
      (volume.restrict (Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    have h1 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1)) (Ioi 0) := by
      intro t ht
      apply ContinuousAt.continuousWithinAt
      exact (continuousAt_cpow_const (b := (σ : ℂ) - 1)
        (Complex.ofReal_mem_slitPlane.2 (ht : (0:ℝ) < t))).comp
          Complex.continuous_ofReal.continuousAt
    have h2 : ContinuousOn (fun t => phi a h t - a 0) (Ioi 0) :=
      (continuousOn_phi a h hh K A m hK).sub continuousOn_const
    exact ContinuousOn.smul (f := fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1))
      (g := fun t => phi a h t - a 0) h1 h2
  refine ⟨hmeas, ?_⟩
  -- finiteness of the lintegral
  have hbound : ∀ t ∈ Ioi (0:ℝ), ‖(t : ℂ) ^ ((σ : ℂ) - 1) • (phi a h t - a 0)‖ₑ ≤
      ∑' n, ENNReal.ofReal (g n t) := by
    intro t ht
    have ht' : (0:ℝ) < t := ht
    have hs := (hasSum_phi_sub a h hh K A m hK ht').const_smul ((t : ℂ) ^ ((σ : ℂ) - 1))
    rw [← hs.tsum_eq]
    refine le_trans enorm_tsum_le_tsum_enorm (ENNReal.tsum_le_tsum fun n => ?_)
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simp only [hg]
    rw [norm_smul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    rw [show -pp h n * t = -(pp h n * t) by ring]
    nlinarith [norm_nonneg (aa a n), Real.rpow_nonneg ht'.le (σ - 1), Real.exp_pos (-(pp h n * t))]
  have hlin : ∫⁻ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((σ : ℂ) - 1) • (phi a h t - a 0)‖ₑ ≤
      ∑' n, ENNReal.ofReal (Real.Gamma σ * (‖aa a n‖ / (pp h n) ^ σ)) := by
    calc ∫⁻ t in Ioi (0:ℝ), ‖(t : ℂ) ^ ((σ : ℂ) - 1) • (phi a h t - a 0)‖ₑ
        ≤ ∫⁻ t in Ioi (0:ℝ), ∑' n, ENNReal.ofReal (g n t) :=
          setLIntegral_mono_ae' measurableSet_Ioi (Filter.Eventually.of_forall hbound)
      _ = ∑' n, ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (g n t) := by
          apply lintegral_tsum
          intro n
          apply Measurable.aemeasurable
          apply ENNReal.measurable_ofReal.comp
          simp only [hg]
          fun_prop
      _ = ∑' n, ENNReal.ofReal (Real.Gamma σ * (‖aa a n‖ / (pp h n) ^ σ)) := by
          congr 1
          funext n
          obtain ⟨hi, he⟩ := integral_term_norm a h hh hσ0 n
          rw [← he]
          rw [ofReal_integral_eq_lintegral_ofReal hi]
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht' : (0:ℝ) < t := ht
          simp only [Pi.zero_apply, hg]
          positivity
  have hsum : Summable (fun n => Real.Gamma σ * (‖aa a n‖ / (pp h n) ^ σ)) :=
    (summable_aa_div a c h hc hh hgrowth hσ).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by
      have := Real.Gamma_pos_of_pos hσ0
      have : 0 ≤ ‖aa a n‖ / (pp h n) ^ σ :=
        div_nonneg (norm_nonneg _) (Real.rpow_nonneg (by unfold pp; positivity) _)
      positivity) hsum] at hlin
  exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top

lemma k_le_of_a0_ne (a : ℕ → ℂ) (c h k : ℝ) (C : ℂ) (hc : 0 < c) (hh : 0 < h) (hk : 0 < k)
    (hC : C = 1 ∨ C = -1) (hgrowth : HeckeCoeffGrowth a c) (hA : HeckeAutomorphic a h k C)
    (K A : ℝ) (m : ℕ) (hK : ∀ n : ℕ, ‖a n‖ ≤ K * (n : ℝ) ^ m + A) (ha0 : a 0 ≠ 0) :
    k ≤ c + 1 := by
  by_contra hlt
  push Not at hlt
  set σ := (c + 1 + k) / 2 with hσdef
  have hσ1 : c + 1 < σ := by linarith
  have hσ2 : σ < k := by linarith
  have hconv := mellinConvergent_phi_sub a c h hc hh hgrowth K A m hK hσ1
  have hCn : ‖C‖ = 1 := by rcases hC with rfl | rfl <;> simp
  obtain ⟨S, hS⟩ := phi_sub_bound a h hh K A m hK
  have ha0p : 0 < ‖a 0‖ := norm_pos_iff.2 ha0
  have hev1 : ∀ᶠ y : ℝ in atTop, S * Real.exp (-(2 * π / h) * (y - 1)) ≤ ‖a 0‖ / 4 := by
    have hβ : 0 < 2 * π / h := by positivity
    have ht : Tendsto (fun y : ℝ => S * Real.exp (-(2 * π / h) * (y - 1))) atTop (𝓝 (S * 0)) := by
      apply Tendsto.const_mul
      apply Real.tendsto_exp_atBot.comp
      apply Tendsto.neg_mul_atTop (by linarith) tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ _ tendsto_id
    rw [mul_zero] at ht
    exact ht.eventually (ge_mem_nhds (by linarith))
  have hev2 : ∀ᶠ y : ℝ in atTop, (4 : ℝ) ≤ y ^ k :=
    (tendsto_rpow_atTop hk).eventually (eventually_ge_atTop 4)
  obtain ⟨Y, hY⟩ := (hev1.and (hev2.and (eventually_ge_atTop (1:ℝ)))).exists_forall_of_atTop
  have hY1 : (1:ℝ) ≤ Y := (hY Y le_rfl).2.2
  set t0 := 1 / Y with ht0def
  have ht0 : 0 < t0 := by positivity
  have hlow : ∀ t ∈ Ioo (0:ℝ) t0,
      ‖a 0‖ / 2 * t ^ (σ - 1 - k) ≤ ‖(t : ℂ) ^ ((σ : ℂ) - 1) • (phi a h t - a 0)‖ := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    set y := 1 / t with hy
    have hy0 : 0 < y := by positivity
    have hyY : Y ≤ y := by
      rw [hy, le_div_iff₀ ht1]
      rw [ht0def, lt_div_iff₀ (by linarith)] at ht2
      linarith
    obtain ⟨hy1, hy2, hy3⟩ := hY y hyY
    have hfe := phi_feq a h k C hA hy0
    have hty : 1 / y = t := by rw [hy]; field_simp
    rw [hty] at hfe
    have hphiy : 3 / 4 * ‖a 0‖ ≤ ‖phi a h y‖ := by
      have := hS y hy3
      have h2 : ‖a 0‖ ≤ ‖phi a h y‖ + ‖phi a h y - a 0‖ := by
        calc ‖a 0‖ = ‖phi a h y - (phi a h y - a 0)‖ := by ring_nf
          _ ≤ ‖phi a h y‖ + ‖phi a h y - a 0‖ := norm_sub_le _ _
      linarith
    have hnorm1 : ‖phi a h t‖ = y ^ k * ‖phi a h y‖ := by
      rw [hfe, norm_smul, norm_mul, hCn, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos hy0 k), one_mul]
    have hlow1 : ‖a 0‖ / 2 * y ^ k ≤ ‖phi a h t - a 0‖ := by
      have h3 : ‖phi a h t‖ ≤ ‖phi a h t - a 0‖ + ‖a 0‖ := by
        calc ‖phi a h t‖ = ‖(phi a h t - a 0) + a 0‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      rw [hnorm1] at h3
      nlinarith
    have hyk : y ^ k = t ^ (-k) := by
      rw [hy, Real.rpow_neg ht1.le, one_div, Real.inv_rpow ht1.le]
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht1]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    rw [hyk] at hlow1
    have e : t ^ (σ - 1 - k) = t ^ (σ - 1) * t ^ (-k) := by
      rw [← Real.rpow_add ht1]; ring_nf
    rw [e]
    have := Real.rpow_pos_of_pos ht1 (σ - 1)
    nlinarith
  have hint2 : IntegrableOn (fun t : ℝ => ‖a 0‖ / 2 * t ^ (σ - 1 - k)) (Ioo 0 t0) := by
    have hc' : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((σ : ℂ) - 1) • (phi a h t - a 0)) (Ioi 0) :=
      hconv
    refine Integrable.mono' (IntegrableOn.mono_set hc'.norm Ioo_subset_Ioi_self) ?_ ?_
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
      intro t ht
      apply ContinuousAt.continuousWithinAt
      exact (Real.continuousAt_rpow_const _ _ (Or.inl ht.1.ne')).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := ht.1; positivity)]
      exact hlow t ht
  have hint3 : IntegrableOn (fun t : ℝ => t ^ (σ - 1 - k)) (Ioo 0 t0) := by
    have := hint2.const_mul (2 / ‖a 0‖)
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioo
    field_simp
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff ht0).1 hint3
  linarith

lemma mellin_bdd (f : ℝ → ℂ) (hf : ∀ σ : ℝ, MellinConvergent f (σ : ℂ)) (σ₁ σ₂ : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖mellin f s‖ ≤ M := by
  have h1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((σ₁ : ℂ) - 1) • f t) (Ioi 0) := hf σ₁
  have h2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((σ₂ : ℂ) - 1) • f t) (Ioi 0) := hf σ₂
  have hg := h1.norm.add h2.norm
  refine ⟨∫ t in Ioi (0:ℝ), (‖(t : ℂ) ^ ((σ₁ : ℂ) - 1) • f t‖ + ‖(t : ℂ) ^ ((σ₂ : ℂ) - 1) • f t‖),
    fun s hs1 hs2 => ?_⟩
  unfold mellin
  apply norm_integral_le_of_norm_le hg
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0:ℝ) < t := ht
  simp only [Pi.add_apply]
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.sub_re,
    Complex.ofReal_re, Complex.one_re]
  have hf0 := norm_nonneg (f t)
  have p1 := Real.rpow_nonneg ht'.le (σ₁ - 1)
  have p2 := Real.rpow_nonneg ht'.le (σ₂ - 1)
  rcases le_or_gt t 1 with ht1 | ht1
  · have : t ^ (s.re - 1) ≤ t ^ (σ₁ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht' ht1 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right this hf0, mul_nonneg p2 hf0]
  · have : t ^ (s.re - 1) ≤ t ^ (σ₂ - 1) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right this hf0, mul_nonneg p1 hf0]

theorem _root_.solution
    (a : ℕ → ℂ) (c h k : ℝ) (C : ℂ)
    (hc : 0 < c) (hh : 0 < h) (hk : 0 < k) (hC : C = 1 ∨ C = -1)
    (hgrowth : HeckeCoeffGrowth a c) :
    HeckeAutomorphic a h k C → HeckeNice a h k C (c + 1) := by
  intro hA
  obtain ⟨K, hK0, m, hK⟩ := coeff_bound a c hc hgrowth
  have hC0 : C ≠ 0 := by rcases hC with rfl | rfl <;> norm_num
  have hCinv : C⁻¹ = C := by rcases hC with rfl | rfl <;> norm_num
  let P : WeakFEPair ℂ :=
    { f := phi a h, g := phi a h, k := k, ε := C, f₀ := a 0, g₀ := a 0,
      hf_int := (continuousOn_phi a h hh K (‖a 0‖) m hK).locallyIntegrableOn measurableSet_Ioi,
      hg_int := (continuousOn_phi a h hh K (‖a 0‖) m hK).locallyIntegrableOn measurableSet_Ioi,
      hk := hk, hε := hC0,
      h_feq := fun x hx => phi_feq a h k C hA hx,
      hf_top := phi_isBigO a h hh K (‖a 0‖) m hK,
      hg_top := phi_isBigO a h hh K (‖a 0‖) m hK }
  refine ⟨P.Λ₀, P.differentiable_Λ₀, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨_, hmel⟩ := mellin_phi_sub a c h hc hh hgrowth K (‖a 0‖) m hK hs
    by_cases ha0 : a 0 = 0
    · have hΛ₀ : P.Λ₀ s = mellin (fun t => phi a h t - a 0) s := by
        unfold WeakFEPair.Λ₀ mellin
        refine integral_congr_ae <| (ae_restrict_iff' measurableSet_Ioi).mpr ?_
        filter_upwards [compl_mem_ae_iff.mpr (Subsingleton.measure_zero (s := {(1:ℝ)})
          (by simp) _)] with t (ht₁ : t ≠ 1) (ht₀ : 0 < t)
        congr 1
        simp only [WeakFEPair.f_modif, P, ha0, Pi.add_apply, smul_zero, sub_zero]
        rcases lt_or_gt_of_ne ht₁ with ht | ht
        · rw [indicator_of_notMem (by simp; linarith), indicator_of_mem (by simp; constructor <;> linarith)]
          simp
        · rw [indicator_of_mem (by simpa using ht), indicator_of_notMem (by simp; intro; linarith)]
          simp
      rw [hΛ₀, hmel, ha0]
      simp
    · have hkc := k_le_of_a0_ne a c h k C hc hh hk hC hgrowth hA K (‖a 0‖) m hK ha0
      have hks : P.k < s.re := by
        show k < s.re
        linarith
      have hm := P.hasMellin hks
      have hΛ : P.Λ s = heckeCompletedLSeries a h s := by
        rw [← hm.2]
        exact hmel
      rw [P.Λ₀_eq, hΛ]
      simp only [smul_eq_mul, P]
      ring
  · intro σ₁ σ₂
    have hstrong := P.isStrongFEPair_toStrongFEPair
    exact mellin_bdd P.f_modif (fun σ => (hstrong.hasMellin (σ : ℂ)).1) σ₁ σ₂
  · intro s
    have hsymm : P.symm.Λ₀ = P.Λ₀ := by
      unfold WeakFEPair.Λ₀
      congr 1
      funext t
      simp only [WeakFEPair.f_modif, WeakFEPair.symm, P, hCinv]
    have := P.functional_equation₀ s
    rw [hsymm] at this
    simpa [smul_eq_mul, P] using this

end Gelbart
