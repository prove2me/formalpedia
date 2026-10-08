-- Prove2me | solution 2 for ConnesRZ.actual_zero_reciprocal_square_summable
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-06T23:26:03.010989+00:00
-- url     : https://prove2.me/submissions/cdbf68d9-3560-4b7f-8e06-329bc37d0513

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
The window grouping and reciprocal-square convergence proof below reuses
formal-math e1a4e6508154ea59f030480661590a9fe3018011,
zeta23/Zeta23/WeilEF/ZeroSummability.lean and Zeta23/Tail.lean.
The final target retains the existing Connes actual-zero carrier and multiplicities.
-/
import Mathlib
import Definitions.Def_ConnesRZ_weil_defs
import Definitions.Def_Zeta23_Tail
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Zeta23.Tail
theorem LocalCount.ofWindowCount (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    LocalCount (fun ρ : Z.carrier => (ρ : ℂ).im) (fun ρ : Z.carrier => Z.mult ρ) A₀ where
  one_le := hA₀
  window t s hs := by
    classical
    refine le_trans ?_ (hloc t)
    have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hsub : s.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
      intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨ρ, hρ, rfl⟩ := hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨ρ.2, hs ρ hρ⟩
    have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
    rw [Finset.sum_map] at h
    exact_mod_cast h


end Zeta23.Tail
noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Set Filter MeasureTheory

/-! ### γ_ρ bookkeeping -/

lemma gammaOf_re (ρ : ℂ) : (gammaOf ρ).re = ρ.im := by
  simp [gammaOf, Complex.div_I]

lemma gammaOf_im (ρ : ℂ) : (gammaOf ρ).im = 1 / 2 - ρ.re := by
  simp [gammaOf, Complex.div_I]

lemma abs_im_le_norm_gammaOf (ρ : ℂ) : |ρ.im| ≤ ‖gammaOf ρ‖ := by
  rw [← gammaOf_re]; exact Complex.abs_re_le_norm _

/-- For a point of the open strip, |Im γ_ρ| < 1/2. -/
lemma abs_gammaOf_im_lt {ρ : ℂ} (h : 0 < ρ.re ∧ ρ.re < 1) : |(gammaOf ρ).im| < 1 / 2 := by
  rw [gammaOf_im, abs_lt]; constructor <;> linarith [h.1, h.2]

/-- For a point of the closed strip, |Im γ_ρ| ≤ 1/2. -/
lemma abs_gammaOf_im_le {ρ : ℂ} (h : 0 ≤ ρ.re ∧ ρ.re ≤ 1) : |(gammaOf ρ).im| ≤ 1 / 2 := by
  rw [gammaOf_im, abs_le]; constructor <;> linarith [h.1, h.2]

/-! ### The weight series Σ_{n∈ℤ} log(|n|+3)/(1+n²) -/

/-- log(|n| + 3)/(1 + n²) ≤ 4 |n|^{−3/2} for n ≠ 0. -/
lemma weight_le (n : ℤ) (hn : n ≠ 0) :
    Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) ≤ 4 * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have hn0 : (0 : ℝ) < |(n : ℝ)| := by linarith
  -- log y ≤ 2 √y and |n| + 3 ≤ 4|n|, so log(|n|+3) ≤ 2√(4|n|) = 4√|n|
  have h1 := Real.log_le_rpow_div (show (0:ℝ) ≤ |(n:ℝ)| + 3 by positivity)
    (show (0:ℝ) < 1/2 by norm_num)
  have h2 : (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) ≤ (4 * |(n : ℝ)|) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h3 : (4 * |(n : ℝ)|) ^ (1 / 2 : ℝ) = 2 * |(n : ℝ)| ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hn0.le, show (4:ℝ) ^ (1/2:ℝ) = 2 by
      rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
  have hA : Real.log (|(n : ℝ)| + 3) ≤ 4 * |(n : ℝ)| ^ (1 / 2 : ℝ) := by
    have : (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (|(n : ℝ)| + 3) ^ (1 / 2 : ℝ) := by ring
    rw [this] at h1; rw [h3] at h2; linarith
  have hB : 1 / (1 + (n : ℝ) ^ 2) ≤ |(n : ℝ)| ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hn0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast, sq_abs,
      one_div]
    exact inv_anti₀ (by positivity) (by linarith)
  calc Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)
      = Real.log (|(n : ℝ)| + 3) * (1 / (1 + (n : ℝ) ^ 2)) := by ring
    _ ≤ (4 * |(n : ℝ)| ^ (1 / 2 : ℝ)) * |(n : ℝ)| ^ (-2 : ℝ) :=
        mul_le_mul hA hB (by positivity) (by positivity)
    _ = 4 * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
        rw [mul_assoc, ← Real.rpow_add hn0]; norm_num

lemma summable_weight :
    Summable (fun n : ℤ => Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_abs_int_rpow (show (1:ℝ) < 3/2 by norm_num)).mul_left 4) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  have h0 : 0 ≤ Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) :=
    div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact weight_le n hn

/-- The total weight W := Σ'_{n∈ℤ} log(|n|+3)/(1+n²). -/
def totalWeight : ℝ := ∑' n : ℤ, Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)

/-! ### zero_sum_inv_sq -/

/-- unit-window key of an ordinate: n := ⌈y⌉ − 1, so that n < y ≤ n + 1. -/
def key (y : ℝ) : ℤ := ⌈y⌉ - 1

lemma key_lt (y : ℝ) : (key y : ℝ) < y := by
  have := Int.ceil_lt_add_one y; unfold key; push_cast; linarith

lemma le_key_add_one (y : ℝ) : y ≤ (key y : ℝ) + 1 := by
  have := Int.le_ceil y; unfold key; push_cast; linarith

/-- if n < y ≤ n+1 then 1 + y² ≥ (1 + n²)/4. -/
lemma one_add_sq_ge {y : ℝ} {n : ℤ} (h1 : (n : ℝ) < y) (h2 : y ≤ (n : ℝ) + 1) :
    (1 + (n : ℝ) ^ 2) / 4 ≤ 1 + y ^ 2 := by
  rcases le_or_gt 0 (n : ℝ) with hn | hn
  · nlinarith
  · have hn' : n < 0 := by exact_mod_cast hn
    have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    have hy : ((n : ℝ) + 1) ^ 2 ≤ y ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0:ℝ) ≤ -(y + ((n : ℝ) + 1)))]
    nlinarith [hy, sq_nonneg ((n : ℝ) + 4 / 3)]

/-! ### The generic theorems (any ZeroConfig with the local count) -/

/-- **Σ_ρ m_ρ/(1+|γ_ρ|²) converges** for ANY zero configuration with a two-sided local count
N(t,t+1] ≤ A₀ log(|t|+3) (dyadic/unit-window summation of the local count). -/
theorem zero_sum_inv_sq_gen (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc' : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    Summable (fun ρ : Z.carrier =>
      (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
  classical
  have hLC := Tail.LocalCount.ofWindowCount Z hA₀ hloc'
  have hW := summable_weight
  refine summable_of_sum_le (c := 4 * A₀ * totalWeight) (fun ρ => div_nonneg (Nat.cast_nonneg _)
    (by linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))])) fun s => ?_
  -- group by the window key of Im ρ
  set κ : Z.carrier → ℤ := fun ρ => key (ρ : ℂ).im with hκ
  rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ) (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
  have hfiber : ∀ n ∈ s.image κ,
      ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
        ≤ 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by
    intro n _
    have hwin := hLC.window n (s.filter fun ρ => κ ρ = n) (fun ρ hρ => by
      simp only [Finset.mem_filter] at hρ
      rw [← hρ.2]; exact ⟨key_lt _, le_key_add_one _⟩)
    have hpt : ∀ ρ ∈ s.filter (fun ρ => κ ρ = n),
        (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
          ≤ (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) := by
      intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have h1 : (n : ℝ) < (ρ : ℂ).im := by rw [← hρ.2]; exact key_lt _
      have h2 : (ρ : ℂ).im ≤ (n : ℝ) + 1 := by rw [← hρ.2]; exact le_key_add_one _
      have hge := one_add_sq_ge h1 h2
      have hnorm : 1 + ((ρ : ℂ).im) ^ 2 ≤ 1 + Complex.normSq (gammaOf ρ) := by
        rw [Complex.normSq_apply, gammaOf_re]; nlinarith [sq_nonneg ((gammaOf (ρ:ℂ)).im)]
      have hm : (0 : ℝ) ≤ Z.mult (ρ : ℂ) := Nat.cast_nonneg _
      have hN0 : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
        linarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
      have hinv : 1 / (1 + Complex.normSq (gammaOf (ρ : ℂ))) ≤ 4 / (1 + (n : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ hN0 (by positivity)]; nlinarith [hge, hnorm]
      calc (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
          = (Z.mult (ρ : ℂ) : ℝ) * (1 / (1 + Complex.normSq (gammaOf (ρ : ℂ)))) := by ring
        _ ≤ (Z.mult (ρ : ℂ) : ℝ) * (4 / (1 + (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left hinv hm
        _ = (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) := by ring
    calc ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
        ≤ ∑ ρ ∈ s with κ ρ = n, (4 / (1 + (n : ℝ) ^ 2)) * (Z.mult ρ : ℝ) :=
          Finset.sum_le_sum hpt
      _ = (4 / (1 + (n : ℝ) ^ 2)) * ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (4 / (1 + (n : ℝ) ^ 2)) * (A₀ * Real.log (|(n:ℝ)| + 3)) :=
          mul_le_mul_of_nonneg_left hwin (by positivity)
      _ = 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) := by ring
  calc ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n, (Z.mult (ρ : ℂ) : ℝ) / (1 + Complex.normSq (gammaOf ρ))
      ≤ ∑ n ∈ s.image κ, 4 * A₀ * (Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2)) :=
        Finset.sum_le_sum hfiber
    _ = 4 * A₀ * ∑ n ∈ s.image κ, Real.log (|(n : ℝ)| + 3) / (1 + (n : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * A₀ * totalWeight := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact hW.sum_le_tsum _ fun n _ =>
          div_nonneg (Real.log_nonneg (by linarith [abs_nonneg (n : ℝ)])) (by positivity)


end WeilEF
end Zeta23

theorem solution : Summable (fun ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} =>
      (ConnesRZ.zeroMult ρ.1 : ℝ) / (1 + Complex.normSq ((ρ.1 - 1 / 2) / Complex.I))) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  exact Zeta23.WeilEF.zero_sum_inv_sq_gen (Zeta23.zetaZeros Zeta23.zetaSeam)
    hA₀ (fun t => hloc t)

#print axioms solution
