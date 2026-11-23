-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.NonemptyCut.tree_cut_wrapper_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:51:41.915558+00:00
-- url     : https://prove2.me/submissions/599b461c-7175-4f2e-9885-4a5da8898ec2

import Definitions.Def_DecrAlmostLinearSSSP_TreeCutProtocol

set_option autoImplicit false
open scoped ENNReal NNReal Topology
open Filter
open DecrAlmostLinearSSSP.Decremental

namespace DecrAlmostLinearSSSP.Decremental.NonemptyCut

lemma tendsto_cut_log_atTop :
    Tendsto (fun m : ℕ => Real.log (max 2 m : ℕ)) atTop atTop := by
  apply Real.tendsto_log_atTop.comp
  have hnat : Tendsto (fun m : ℕ => max 2 m) atTop atTop := by
    apply tendsto_atTop_mono (fun m => le_max_right 2 m)
    exact tendsto_id
  exact tendsto_natCast_atTop_atTop.comp hnat

lemma log_ratio_const (c : ℝ) :
    Tendsto (fun m : ℕ => c / Real.log (max 2 m : ℕ)) atTop (nhds 0) := by
  have hz := Tendsto.inv_tendsto_atTop tendsto_cut_log_atTop
  simpa only [div_eq_mul_inv, Pi.inv_apply, mul_zero] using hz.const_mul c

lemma subpolynomial_const_mul {f : ℕ → ℝ} (c : ℝ) (hc : 0 < c)
    (hf : Subpolynomial f) : Subpolynomial (fun m => c * f m) := by
  rcases hf with ⟨hfpos, hflim⟩
  constructor
  · intro m
    exact mul_pos hc (hfpos m)
  · have hconst := log_ratio_const (Real.log c)
    have heq : (fun m => Real.log (c * f m) / Real.log (max 2 m : ℕ)) =
        (fun m => Real.log c / Real.log (max 2 m : ℕ) +
          Real.log (f m) / Real.log (max 2 m : ℕ)) := by
      funext m
      rw [Real.log_mul hc.ne' (hfpos m).ne']
      ring
    rw [heq]
    simpa using hconst.add hflim

lemma subpolynomial_one : Subpolynomial (fun _ : ℕ => (1 : ℝ)) := by
  constructor
  · intro m
    norm_num
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

lemma subpolynomial_add_one {f : ℕ → ℝ} (hf : Subpolynomial f) :
    Subpolynomial (fun m => 1 + f m) := by
  rcases hf with ⟨hfpos, hflim⟩
  have habs : Tendsto (fun m => |Real.log (f m) / Real.log (max 2 m : ℕ)|)
      atTop (nhds 0) := by simpa using hflim.abs
  have hsum := (log_ratio_const (Real.log 2)).add habs
  rw [zero_add] at hsum
  have habs' : Tendsto (fun m => |Real.log (1 + f m) / Real.log (max 2 m : ℕ)|)
      atTop (nhds 0) := by
    apply squeeze_zero' (g := fun m => Real.log 2 / Real.log (max 2 m : ℕ) +
      |Real.log (f m) / Real.log (max 2 m : ℕ)|)
    · filter_upwards with m
      exact abs_nonneg _
    · filter_upwards with m
      have hM : (2 : ℝ) ≤ (max 2 m : ℕ) := by exact_mod_cast le_max_left 2 m
      have hL : 0 < Real.log (max 2 m : ℕ) := Real.log_pos (by linarith)
      have hf0 := hfpos m
      by_cases hf1 : f m ≤ 1
      · have hlo : 0 ≤ Real.log (1 + f m) := Real.log_nonneg (by linarith)
        have hhi : Real.log (1 + f m) ≤ Real.log 2 := by
          apply Real.log_le_log (by linarith)
          linarith
        rw [abs_of_nonneg (div_nonneg hlo hL.le)]
        have hrest : 0 ≤ |Real.log (f m) / Real.log (max 2 m : ℕ)| := abs_nonneg _
        exact (div_le_div_of_nonneg_right hhi hL.le).trans (by linarith)
      · have hfge : 1 ≤ f m := le_of_not_ge hf1
        have hflog : 0 ≤ Real.log (f m) := Real.log_nonneg hfge
        have hlo : 0 ≤ Real.log (1 + f m) := Real.log_nonneg (by linarith)
        have hhi : Real.log (1 + f m) ≤ Real.log 2 + Real.log (f m) := by
          rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hf0)]
          apply Real.log_le_log (by linarith)
          linarith
        rw [abs_of_nonneg (div_nonneg hlo hL.le), abs_of_nonneg (div_nonneg hflog hL.le)]
        apply (div_le_div_of_nonneg_right hhi hL.le).trans
        rw [add_div]
    · exact hsum
  constructor
  · intro m
    linarith [hfpos m]
  · rwa [tendsto_zero_iff_abs_tendsto_zero]

lemma subpolynomial_max_const {f : ℕ → ℝ} (c : ℝ) (hc : 0 < c)
    (hf : Subpolynomial f) : Subpolynomial (fun m => max c (f m)) := by
  rcases hf with ⟨hfpos, hflim⟩
  have habs : Tendsto (fun m => |Real.log (f m) / Real.log (max 2 m : ℕ)|)
      atTop (nhds 0) := by simpa using hflim.abs
  have hsum := (log_ratio_const |Real.log c|).add habs
  rw [zero_add] at hsum
  have habs' : Tendsto (fun m => |Real.log (max c (f m)) /
      Real.log (max 2 m : ℕ)|) atTop (nhds 0) := by
    apply squeeze_zero' (g := fun m => |Real.log c| / Real.log (max 2 m : ℕ) +
      |Real.log (f m) / Real.log (max 2 m : ℕ)|)
    · filter_upwards with m
      exact abs_nonneg _
    · filter_upwards with m
      have hM : (2 : ℝ) ≤ (max 2 m : ℕ) := by exact_mod_cast le_max_left 2 m
      have hL : 0 < Real.log (max 2 m : ℕ) := Real.log_pos (by linarith)
      by_cases hfcf : f m ≤ c
      · rw [max_eq_left hfcf]
        have hrest : 0 ≤ |Real.log (f m) / Real.log (max 2 m : ℕ)| := abs_nonneg _
        rw [abs_div, abs_of_pos hL]
        exact le_add_of_nonneg_right hrest
      · rw [max_eq_right (le_of_not_ge hfcf)]
        have hconst : 0 ≤ |Real.log c| / Real.log (max 2 m : ℕ) :=
          div_nonneg (abs_nonneg _) hL.le
        exact le_add_of_nonneg_left hconst
    · exact hsum
  constructor
  · intro m
    exact lt_of_lt_of_le hc (le_max_left _ _)
  · rwa [tendsto_zero_iff_abs_tendsto_zero]

lemma quality_exponent_half (m : ℕ) :
    (1 / 2 : ℝ) ≤ Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
      max 1 (Real.log (Real.log (max 2 m : ℕ))) := by
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
    have hinv : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [hinv] at h
    linarith
  have hM : (2 : ℝ) ≤ (max 2 m : ℕ) := by exact_mod_cast le_max_left 2 m
  have hL : (1 / 2 : ℝ) ≤ Real.log (max 2 m : ℕ) := by
    exact htwo.trans (Real.log_le_log (by norm_num) hM)
  have hp : (0 : ℝ) ≤ 5 / 6 := by norm_num
  have hbase : Real.rpow (1 / 2 : ℝ) (5 / 6 : ℝ) ≤
      Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) := by
    exact Real.rpow_le_rpow (by norm_num) hL hp
  have hself : (1 / 2 : ℝ) ≤ Real.rpow (1 / 2 : ℝ) (5 / 6 : ℝ) := by
    calc
      (1 / 2 : ℝ) = Real.rpow (1 / 2) 1 := (Real.rpow_one _).symm
      _ ≤ Real.rpow (1 / 2) (5 / 6) := by
        exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
  have hmax : (1 : ℝ) ≤ max 1 (Real.log (Real.log (max 2 m : ℕ))) := le_max_left _ _
  calc
    (1 / 2 : ℝ) ≤ Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) := hself.trans hbase
    _ = Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) * 1 := by ring
    _ ≤ Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
        max 1 (Real.log (Real.log (max 2 m : ℕ))) := by
      apply mul_le_mul_of_nonneg_left hmax
      exact Real.rpow_nonneg (by linarith) _

end DecrAlmostLinearSSSP.Decremental.NonemptyCut

open DecrAlmostLinearSSSP.Decremental.NonemptyCut

/-- Explicit subpolynomial parameters and arithmetic envelope for the public wrapper. -/
theorem solution (K₀ h₀ a₀ : ℕ → ℝ) (C₀ : ℝ)
    (hC₀ : 0 < C₀) (hK₀ : Subpolynomial K₀) (hh₀ : Subpolynomial h₀)
    (ha₀ : Subpolynomial a₀)
    (hquality : ∀ m, K₀ m ≤ Real.rpow 2
      (C₀ * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
        max 1 (Real.log (Real.log (max 2 m : ℕ))))) :
    ∃ (K h Γ a : ℕ → ℝ) (C : ℝ),
      0 < C ∧ Subpolynomial K ∧ Subpolynomial h ∧ Subpolynomial Γ ∧ Subpolynomial a ∧
      (∀ m, 32 ≤ K m ∧ K m ≤ Real.rpow 2
        (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
          max 1 (Real.log (Real.log (max 2 m : ℕ))))) ∧
      K = (fun m => max 32 (K₀ m)) ∧ h = (fun m => 64 * (1 + h₀ m)) ∧
      Γ = (fun _ => 1) ∧ a = (fun m => 16 * (1 + a₀ m)) ∧ C = C₀ + 16 ∧
      ∀ (m : ℕ) (q R W : ℝ), 0 ≤ q → 0 ≤ R → 0 ≤ W →
        W ≤ 7 * (C₀ * m * a₀ m + h₀ m * (2 * q + 2 * R)) + 32 * m + 40 * (q + R) →
        W + 6 * q ≤ C * m * a m + h m * (q + R) := by
  let K : ℕ → ℝ := fun m => max 32 (K₀ m)
  let h : ℕ → ℝ := fun m => 64 * (1 + h₀ m)
  let Γ : ℕ → ℝ := fun _ => 1
  let a : ℕ → ℝ := fun m => 16 * (1 + a₀ m)
  let C : ℝ := C₀ + 16
  have hC : 0 < C := by dsimp [C]; linarith
  have hK : Subpolynomial K := subpolynomial_max_const 32 (by norm_num) hK₀
  have hh : Subpolynomial h := subpolynomial_const_mul 64 (by norm_num)
    (subpolynomial_add_one hh₀)
  have hΓ : Subpolynomial Γ := subpolynomial_one
  have ha : Subpolynomial a := subpolynomial_const_mul 16 (by norm_num)
    (subpolynomial_add_one ha₀)
  refine ⟨K, h, Γ, a, C, hC, hK, hh, hΓ, ha, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · intro m
    let L : ℝ := Real.log (max 2 m : ℕ)
    let A : ℝ := Real.rpow L (5 / 6 : ℝ) * max 1 (Real.log L)
    have hA : (1 / 2 : ℝ) ≤ A := quality_exponent_half m
    have hA0 : 0 ≤ A := by linarith
    have hKquality : K₀ m ≤ Real.rpow 2 ((C₀ + 16) * A) := by
      apply (hquality m).trans
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      calc
        C₀ * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
            max 1 (Real.log (Real.log (max 2 m : ℕ))) = C₀ * A := by
          dsimp [A, L]
          ring
        _ ≤ (C₀ + 16) * A := by nlinarith
    have h32 : (32 : ℝ) ≤ Real.rpow 2 ((C₀ + 16) * A) := by
      calc
        (32 : ℝ) ≤ (2 : ℝ) ^ (8 : ℕ) := by norm_num
        _ = Real.rpow 2 (8 : ℝ) := (Real.rpow_natCast 2 8).symm
        _ ≤ Real.rpow 2 (16 * A) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          linarith
        _ ≤ Real.rpow 2 ((C₀ + 16) * A) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          nlinarith
    refine ⟨le_max_left _ _, max_le ?_ ?_⟩
    · simpa only [C, A, L, mul_assoc] using h32
    · simpa only [C, A, L, mul_assoc] using hKquality
  · intro m q R W hq hR hW hbound
    have hma : 0 ≤ (m : ℝ) := by positivity
    have ha0 : 0 < a₀ m := ha₀.1 m
    have hh0 : 0 < h₀ m := hh₀.1 m
    dsimp [C, a, h]
    have hqa : 0 ≤ q + R := by linarith
    have hterm : 7 * (C₀ * m * a₀ m) ≤ (C₀ + 16) * m * (16 * (1 + a₀ m)) := by
      nlinarith [mul_nonneg hC₀.le hma, mul_nonneg hC₀.le ha0.le, mul_nonneg hma ha0.le]
    nlinarith [mul_nonneg hh0.le hqa, mul_nonneg ha0.le hma]
