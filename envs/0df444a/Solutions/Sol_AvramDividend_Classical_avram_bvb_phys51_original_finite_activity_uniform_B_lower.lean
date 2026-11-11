-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys51_original_finite_activity_uniform_B_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:21:09.640081+00:00
-- url     : https://prove2.me/submissions/49685ab9-f2f2-4973-a74d-a1785bec623e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finitecap_generator_residual_floor
import Theorems.Thm_AvramDividend_Classical_avram_bv_finite734_fullcap_negative_mark_envelope
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0) (hgrid : ∀ n, u n 0 = 0 ∧ ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) (B : ℕ → Ω → ℝ) (hB : ∀ n ω, let Z : ℕ → ℝ := fun i => Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i); B n ω = (∑ i ∈ Finset.range (n + 1), if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then Real.exp (-(q * (u n i : ℝ))) * (X.generator w (Z i) - q * w (Z i)) * ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) + (let J : ℝ≥0 → ℝ := fun t => ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0; let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t; ∑ i ∈ Finset.range (n + 1), (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z i ∧ ENNReal.ofReal (Z i) < C then Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i) else 0) * (R (u n i) - R (u n (i + 1))))) (hAllB : ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0) (hPre : ∀ᵐ ω ∂P, ∀ n i, Function.leftLim (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n (i + 1)) = riskProcess X x D (u n (i + 1)) ω) (hFinite : C ≠ ⊤) (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ ω ∂P, ∀ n : ℕ, -K ≤ B n ω := by
  classical
  obtain ⟨W, hWnonneg, hW⟩ :=
    avram_bv_finite734_fullcap_negative_mark_envelope
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad hActivity hFinite
  have hw_upper (y : ℝ) (hy : y ∈ Icc (0 : ℝ) C.toReal) :
      w y ≤ W := by
    have hz : -y - 1 < 0 := by have := hy.1; linarith
    have hyz : y + (-y - 1) < 0 := by ring_nf; norm_num
    have h := hW y (-y - 1) hy hz
    rw [hw_neg (y + (-y - 1)) hyz] at h
    have habs : |w y| ≤ W := by simpa only [zero_sub, abs_neg] using h
    exact (le_abs_self (w y)).trans habs
  have hdrift : 0 ≤ X.drift :=
    le_of_lt (bv_standing_drift_pos X hX hBV).1
  let L : ℝ := (X.ν (Iio (0 : ℝ))).toReal + q
  have hL : 0 ≤ L := by
    dsimp [L]
    exact add_nonneg ENNReal.toReal_nonneg (le_of_lt hq)
  have hR :=
    avram_redux11_original_BV_raw_removed_residual_zero_ae X hX hBV
  refine ⟨L * W * T, mul_nonneg (mul_nonneg hL hWnonneg) (le_of_lt hT), ?_⟩
  filter_upwards [hR] with ω hω
  intro n
  let Z : ℕ → ℝ := fun i => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  let dt : ℕ → ℝ := fun i =>
    (u n (i + 1) : ℝ) - (u n i : ℝ)
  let a : ℕ → ℝ := fun i =>
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z i ∧ ENNReal.ofReal (Z i) < C then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator w (Z i) - q * w (Z i)) * dt i
    else 0
  have hcell (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      -(L * W) * dt i ≤ a i := by
    have hstep : 0 ≤ dt i := by
      have hmono_i := hmono n i (Finset.mem_range.mp hi)
      exact sub_nonneg.mpr (by exact_mod_cast hmono_i)
    dsimp [a]
    split_ifs with hm
    · rcases hm with ⟨_, hy, hyC⟩
      have hcap : Z i ≤ C.toReal := by
        have ht := ENNReal.toReal_mono hFinite hyC.le
        simpa [ENNReal.toReal_ofReal (le_of_lt hy)] using ht
      have hmem : Z i ∈ Icc (0 : ℝ) C.toReal :=
        ⟨le_of_lt hy, hcap⟩
      have hfloor :=
        avram_bv_correct12_finitecap_generator_residual_floor
          X hBV q w C hC hw_cont hw0 hw_neg hw_smooth
          hw_grad hActivity hdrift (Z i) hy hyC (hw_gen (Z i) hy hyC).1
      have hresle := (hw_gen (Z i) hy hyC).2
      have hfloorW :
          -(L * W) ≤ X.generator w (Z i) - q * w (Z i) := by
        have hprod : 0 ≤ L * (W - w (Z i)) :=
          mul_nonneg hL (sub_nonneg.mpr (hw_upper (Z i) hmem))
        dsimp [L] at hfloor ⊢
        nlinarith
      have hprodq : 0 ≤ q * (u n i : ℝ) :=
        mul_nonneg (le_of_lt hq) (u n i).property
      have hexple : Real.exp (-(q * (u n i : ℝ))) ≤ 1 := by
        calc
          Real.exp (-(q * (u n i : ℝ))) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (neg_nonpos.mpr hprodq)
          _ = 1 := by simp
      have hexp0 : 0 ≤ Real.exp (-(q * (u n i : ℝ))) :=
        le_of_lt (Real.exp_pos _)
      have hres :
          X.generator w (Z i) - q * w (Z i) ≤
            Real.exp (-(q * (u n i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) := by
        have hmult : 0 ≤
            (1 - Real.exp (-(q * (u n i : ℝ)))) *
              (-(X.generator w (Z i) - q * w (Z i))) :=
          mul_nonneg (sub_nonneg.mpr hexple) (neg_nonneg.mpr hresle)
        nlinarith
      exact mul_le_mul_of_nonneg_right (hfloorW.trans hres) hstep
    · have hprod : 0 ≤ L * W * dt i :=
        mul_nonneg (mul_nonneg hL hWnonneg) hstep
      dsimp [dt] at hprod ⊢
      nlinarith
  have hsum :
      -(L * W) *
        (∑ i ∈ Finset.range (n + 1), dt i) ≤
      ∑ i ∈ Finset.range (n + 1), a i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hcell
  have hdt (i : ℕ) : dt i = T / ((n : ℝ) + 2) := by
    dsimp [dt]
    rw [huniform n (i + 1), huniform n i]
    push_cast
    ring
  have hwidth :
      (∑ i ∈ Finset.range (n + 1), dt i) ≤ T := by
    simp_rw [hdt]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hd : 0 ≤ T / ((n : ℝ) + 2) :=
      div_nonneg (le_of_lt hT) (by positivity)
    have hn' : (n + 1 : ℝ) ≤ (n : ℝ) + 2 := by push_cast; linarith
    have hbound := mul_le_mul_of_nonneg_right hn' hd
    have hid : ((n : ℝ) + 2) * (T / ((n : ℝ) + 2)) = T := by field_simp
    simpa only [Nat.cast_add, Nat.cast_one] using hbound.trans_eq hid
  have hsumK :
      -(L * W * T) ≤ ∑ i ∈ Finset.range (n + 1), a i := by
    have hp : 0 ≤ L * W := mul_nonneg hL hWnonneg
    have hz : 0 ≤ L * W *
        (T - ∑ i ∈ Finset.range (n + 1), dt i) :=
      mul_nonneg hp (sub_nonneg.mpr hwidth)
    nlinarith
  have hreszero :
      (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
       let R : ℝ≥0 → ℝ := fun t =>
         ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (n + 1),
         (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z i ∧ ENNReal.ofReal (Z i) < C then
           Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
         else 0) * (R (u n i) - R (u n (i + 1)))) = 0 := by
    dsimp
    apply Finset.sum_eq_zero
    intro i hi
    rw [hω (u n i), hω (u n (i + 1))]
    ring
  have hBn := hB n ω
  dsimp only at hBn
  rw [hreszero, add_zero] at hBn
  change B n ω = (∑ i ∈ Finset.range (n + 1), a i) at hBn
  rw [hBn]
  exact hsumK
