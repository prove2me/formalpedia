-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.NonemptyCut.subpolynomial_wrapper_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:48:18.237814+00:00
-- url     : https://prove2.me/submissions/d5bc94be-d209-4064-adda-35cabe1e3889

import Definitions.Def_DecrAlmostLinearSSSP_TreeCutProtocol

set_option autoImplicit false

open scoped ENNReal NNReal Topology
open Filter
open DecrAlmostLinearSSSP.Decremental

namespace DecrAlmostLinearSSSP.Decremental.NonemptyCut

lemma log_max_of_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (max x y) = max (Real.log x) (Real.log y) := by
  rcases le_total x y with h | h
  · rw [max_eq_right h]
    exact (max_eq_right (Real.log_le_log hx h)).symm
  · rw [max_eq_left h]
    exact (max_eq_left (Real.log_le_log hy h)).symm

lemma max_div_nonneg {a b c : ℝ} (hc : 0 ≤ c) :
    max a b / c = max (a / c) (b / c) := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  · rcases le_total a b with h | h
    · rw [max_eq_right h, max_eq_right (by gcongr : a / c ≤ b / c)]
    · rw [max_eq_left h, max_eq_left (by gcongr : b / c ≤ a / c)]

lemma denominator_tendsto :
    Tendsto (fun m : ℕ => Real.log (max 2 m : ℕ)) atTop atTop := by
  have hc : Tendsto (fun m : ℕ => ((max 2 m : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (l := atTop) (f := fun m : ℕ => (m : ℝ))
      (g := fun m : ℕ => ((max 2 m : ℕ) : ℝ))
    · intro m
      exact_mod_cast Nat.le_max_right 2 m
    · exact tendsto_natCast_atTop_atTop
  exact Real.tendsto_log_atTop.comp hc

lemma denominator_nonneg (m : ℕ) : 0 ≤ Real.log (max 2 m : ℕ) := by
  apply Real.log_nonneg
  exact_mod_cast (show 1 ≤ max 2 m by omega)

lemma subpoly_max_const {f : ℕ → ℝ} (hf : Subpolynomial f) {c : ℝ} (hc : 0 < c) :
    Subpolynomial (fun m => max c (f m)) := by
  constructor
  · intro m
    exact lt_of_lt_of_le hc (le_max_left _ _)
  · have hzero : Tendsto (fun m : ℕ => Real.log c / Real.log (max 2 m : ℕ))
        atTop (nhds 0) := denominator_tendsto.const_div_atTop _
    have hm := hf.2.max hzero
    have heq : (fun m : ℕ => Real.log (max c (f m)) / Real.log (max 2 m : ℕ)) =
        (fun m => max (Real.log (f m) / Real.log (max 2 m : ℕ))
          (Real.log c / Real.log (max 2 m : ℕ))) := by
      funext m
      rw [log_max_of_pos hc (hf.1 m), max_div_nonneg (denominator_nonneg m), max_comm]
    rw [heq]
    simpa using hm

lemma subpoly_max {f g : ℕ → ℝ} (hf : Subpolynomial f) (hg : Subpolynomial g) :
    Subpolynomial (fun m => max (f m) (g m)) := by
  constructor
  · intro m
    exact lt_of_lt_of_le (hf.1 m) (le_max_left _ _)
  · have hm := hf.2.max hg.2
    have heq : (fun m : ℕ => Real.log (max (f m) (g m)) / Real.log (max 2 m : ℕ)) =
        (fun m => max (Real.log (f m) / Real.log (max 2 m : ℕ))
          (Real.log (g m) / Real.log (max 2 m : ℕ))) := by
      funext m
      rw [log_max_of_pos (hf.1 m) (hg.1 m), max_div_nonneg (denominator_nonneg m)]
    rw [heq]
    simpa using hm

lemma subpoly_const_mul {f : ℕ → ℝ} (hf : Subpolynomial f) {c : ℝ} (hc : 0 < c) :
    Subpolynomial (fun m => c * f m) := by
  constructor
  · intro m
    exact mul_pos hc (hf.1 m)
  · have hzero : Tendsto (fun m : ℕ => Real.log c / Real.log (max 2 m : ℕ))
        atTop (nhds 0) := denominator_tendsto.const_div_atTop _
    have hm := hzero.add hf.2
    have heq : (fun m : ℕ => Real.log (c * f m) / Real.log (max 2 m : ℕ)) =
        (fun m => Real.log c / Real.log (max 2 m : ℕ) +
          Real.log (f m) / Real.log (max 2 m : ℕ)) := by
      funext m
      rw [Real.log_mul hc.ne' (hf.1 m).ne', add_div]
    rw [heq]
    simpa using hm

lemma subpoly_one : Subpolynomial (fun _ : ℕ => (1 : ℝ)) := by
  constructor
  · intro m
    norm_num
  · simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))

lemma quality_padding {K₀ : ℕ → ℝ} {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hbound : ∀ m, K₀ m ≤ Real.rpow 2
      (C₀ * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
        max 1 (Real.log (Real.log (max 2 m : ℕ))))) :
    ∃ C : ℝ, 0 < C ∧ ∀ m, max 32 (K₀ m) ≤ Real.rpow 2
      (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
        max 1 (Real.log (Real.log (max 2 m : ℕ)))) := by
  let p : ℝ := Real.rpow (Real.log 2) (5 / 6 : ℝ)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0 < p := Real.rpow_pos_of_pos hlog2 _
  refine ⟨C₀ + 5 / p, add_pos hC₀ (div_pos (by norm_num) hp), ?_⟩
  intro m
  let L : ℝ := Real.log (max 2 m : ℕ)
  let q : ℝ := Real.rpow L (5 / 6 : ℝ) * max 1 (Real.log L)
  have hM : (2 : ℝ) ≤ ((max 2 m : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_max_left 2 m
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hM
  have hpq : p ≤ Real.rpow L (5 / 6 : ℝ) := by
    exact Real.rpow_le_rpow hlog2.le hL (by norm_num)
  have hq_lower : p ≤ q := by
    calc
      p ≤ Real.rpow L (5 / 6 : ℝ) := hpq
      _ = Real.rpow L (5 / 6 : ℝ) * 1 := (mul_one _).symm
      _ ≤ q := mul_le_mul_of_nonneg_left (le_max_left _ _)
        (Real.rpow_nonneg (hlog2.le.trans hL) _)
  have hq : 0 < q := lt_of_lt_of_le hp hq_lower
  have hmul : (5 / p) * p ≤ (5 / p) * q :=
    mul_le_mul_of_nonneg_left hq_lower (div_pos (by norm_num) hp).le
  have h5p : (5 / p) * p = 5 := by field_simp
  have h5 : 5 ≤ (5 / p) * q := by rwa [h5p] at hmul
  have h5C : 5 ≤ (C₀ + 5 / p) * q := by
    calc
      5 ≤ (5 / p) * q := h5
      _ ≤ C₀ * q + (5 / p) * q := le_add_of_nonneg_left (mul_nonneg hC₀.le hq.le)
      _ = (C₀ + 5 / p) * q := by ring
  have hC₀q : C₀ * q ≤ (C₀ + 5 / p) * q := by
    calc
      C₀ * q ≤ C₀ * q + (5 / p) * q :=
        le_add_of_nonneg_right (mul_nonneg (div_pos (by norm_num) hp).le hq.le)
      _ = (C₀ + 5 / p) * q := by ring
  rw [mul_assoc]
  change max 32 (K₀ m) ≤ Real.rpow 2 ((C₀ + 5 / p) * q)
  apply max_le
  · calc
      (32 : ℝ) = (2 : ℝ) ^ 5 := by norm_num
      _ = Real.rpow 2 ((5 : ℕ) : ℝ) := (Real.rpow_natCast 2 5).symm
      _ ≤ Real.rpow 2 ((C₀ + 5 / p) * q) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h5C
  · have hb := hbound m
    rw [mul_assoc] at hb
    change K₀ m ≤ Real.rpow 2 (C₀ * q) at hb
    exact hb.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) hC₀q)

end DecrAlmostLinearSSSP.Decremental.NonemptyCut

open DecrAlmostLinearSSSP.Decremental.NonemptyCut

/-- Supporting parameter algebra for the public tree-cut wrapper. -/
theorem solution {K₀ h₀ a₀ : ℕ → ℝ} {C₀ : ℝ}
    (hC₀ : 0 < C₀) (hK₀ : Subpolynomial K₀) (hh₀ : Subpolynomial h₀)
    (ha₀ : Subpolynomial a₀)
    (hbound : ∀ m, K₀ m ≤ Real.rpow 2
      (C₀ * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
        max 1 (Real.log (Real.log (max 2 m : ℕ))))) :
    ∃ C : ℝ, 0 < C ∧
      Subpolynomial (fun m => max 32 (K₀ m)) ∧
      (∀ c : ℝ, 0 < c → Subpolynomial (fun m => c * max 1 (h₀ m))) ∧
      (∀ c : ℝ, 0 < c → Subpolynomial (fun m => c * max 1 (a₀ m))) ∧
      (∀ c d : ℝ, 0 < c → 0 < d →
        Subpolynomial (fun m => max (c * max 1 (h₀ m)) (d * max 1 (a₀ m)))) ∧
      Subpolynomial (fun _ : ℕ => (1 : ℝ)) ∧
      (∀ m, 32 ≤ max 32 (K₀ m)) ∧
      ∀ m, max 32 (K₀ m) ≤ Real.rpow 2
        (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
          max 1 (Real.log (Real.log (max 2 m : ℕ)))) := by
  obtain ⟨C, hC, hquality⟩ := quality_padding hC₀ hbound
  refine ⟨C, hC, subpoly_max_const hK₀ (by norm_num), ?_, ?_, ?_, subpoly_one, ?_, hquality⟩
  · intro c hc
    exact subpoly_const_mul (subpoly_max_const hh₀ zero_lt_one) hc
  · intro c hc
    exact subpoly_const_mul (subpoly_max_const ha₀ zero_lt_one) hc
  · intro c d hc hd
    exact subpoly_max
      (subpoly_const_mul (subpoly_max_const hh₀ zero_lt_one) hc)
      (subpoly_const_mul (subpoly_max_const ha₀ zero_lt_one) hd)
  · intro m
    exact le_max_left _ _
