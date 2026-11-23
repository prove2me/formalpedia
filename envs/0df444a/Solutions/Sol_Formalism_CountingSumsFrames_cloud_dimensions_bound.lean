-- Prove2me | solution 1 for Formalism.CountingSumsFrames.cloud_dimensions_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:09.421897+00:00
-- url     : https://prove2.me/submissions/cd5742c3-b77d-4dca-bb89-59467bbac361

import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_WeylDimPosOfAntitone
import Theorems.Thm_Formalism_CountingSumsFrames_weylDim_pos_of_antitone
import Theorems.Thm_Formalism_CountingSumsFrames_hwt_pos
import Theorems.Thm_Formalism_CountingSumsFrames_cwt_bound
import Theorems.Thm_Formalism_CountingSumsFrames_hwt_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : CloudDims := by
  refine ⟨8 * Real.exp 8, by positivity, ?_⟩
  intro N m c A B cl b' hanti hcl hb hAB hsize
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set t : ℝ := 4 * c / b' with ht_def
  have ht : 0 ≤ t := by positivity
  have hA : ∀ s, (c : ℝ) ≤ t * A s := fun s => by
    rw [ht_def, div_mul_eq_mul_div, le_div_iff₀ hb]
    have := (hAB s).1
    nlinarith
  have hB : ∀ s, (c : ℝ) ≤ t * B s := fun s => by
    rw [ht_def, div_mul_eq_mul_div, le_div_iff₀ hb]
    have := (hAB s).2
    nlinarith
  set x : ℝ := N * (m + 2) * c / b' with hx_def
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx_def, div_le_one hb]; exact hsize
  have hCx : 8 * Real.exp 8 * N * (m + 2) * c / b' = 8 * Real.exp 8 * x := by
    rw [hx_def]; ring
  set K : ℕ := (2 * m + 1) * N with hK
  have hKt : (K : ℝ) * t ≤ 8 * x := by
    have e1 : (K : ℝ) * t = (4 * ((2 * m + 1) * N * c)) / b' := by
      rw [hK, ht_def]; push_cast; ring
    have e2 : 8 * x = (8 * (N * (m + 2) * c)) / b' := by rw [hx_def]; ring
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ hb.le
    have : 0 ≤ (N : ℝ) * c := by positivity
    nlinarith
  have hE : (1 + t) ^ K ≤ Real.exp (8 * x) := by
    calc (1 + t) ^ K ≤ (Real.exp t) ^ K :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp t]) K
      _ = Real.exp (K * t) := (Real.exp_nat_mul t K).symm
      _ ≤ Real.exp (8 * x) := Real.exp_le_exp.mpr hKt
  have hexp1 : (1 - 8 * x) * Real.exp (8 * x) ≤ 1 := by
    have h1 := Real.add_one_le_exp (-(8 * x))
    have h2 := Real.exp_pos (8 * x)
    calc (1 - 8 * x) * Real.exp (8 * x) ≤ Real.exp (-(8 * x)) * Real.exp (8 * x) :=
          mul_le_mul_of_nonneg_right (by linarith) h2.le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hexp8 : 1 ≤ Real.exp 8 := Real.one_le_exp (by norm_num)
  have hct := fun s => cwt_bound m (A s) c (B s) (cl s) (hanti s) (hcl s) t ht (hA s) (hB s)
  have hPl : 0 < ∏ s, (weylDim m (cl s) : ℝ) :=
    Finset.prod_pos fun s _ => by exact_mod_cast weylDim_pos_of_antitone m (cl s) (hanti s)
  have hPh : 0 < ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ) :=
    Finset.prod_pos fun s _ => hwt_pos m (A s) (B s)
  have hPc0 : 0 ≤ ∏ s, (weylDim (m + 2) (cwt m (A s) c (B s) (cl s)) : ℝ) :=
    Finset.prod_nonneg fun s _ => (hct s).1
  have Pc : ∏ s, (weylDim (m + 2) (cwt m (A s) c (B s) (cl s)) : ℝ) ≤
      (1 + t) ^ K * ((∏ s, (weylDim m (cl s) : ℝ)) * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ)) := by
    calc _ ≤ ∏ s, ((1 + t) ^ (2 * m + 1) *
          ((weylDim m (cl s) : ℝ) * (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ))) :=
          Finset.prod_le_prod (fun s _ => (hct s).1) (fun s _ => (hct s).2)
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, ← pow_mul]
  have Ph : ∏ s, (weylDim (m + 2) (hwt m (A s + c) (B s + c)) : ℝ) ≤
      (1 + t) ^ K * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ) := by
    calc _ ≤ ∏ s, ((1 + t) ^ (2 * m + 1) * (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ)) :=
          Finset.prod_le_prod (fun s _ => (hwt_pos m (A s + c) (B s + c)).le)
            (fun s _ => hwt_bound m (A s) c (B s) t ht (hA s) (hB s))
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [hCx]
  simp only [Rat.cast_prod, Rat.cast_mul]
  refine ⟨?_, ?_⟩
  · set Q := (∏ s, (weylDim m (cl s) : ℝ)) * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ)
    have hQ : 0 ≤ Q := by positivity
    by_cases h : 1 - 8 * Real.exp 8 * x ≤ 0
    · calc (1 - 8 * Real.exp 8 * x) * ∏ s, (weylDim (m + 2) (cwt m (A s) c (B s) (cl s)) : ℝ) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg h hPc0
        _ ≤ Q := hQ
    · rw [not_le] at h
      have hC : 8 * x ≤ 8 * Real.exp 8 * x := by nlinarith
      calc (1 - 8 * Real.exp 8 * x) * ∏ s, (weylDim (m + 2) (cwt m (A s) c (B s) (cl s)) : ℝ)
          ≤ (1 - 8 * Real.exp 8 * x) * ((1 + t) ^ K * Q) := mul_le_mul_of_nonneg_left Pc h.le
        _ ≤ (1 - 8 * Real.exp 8 * x) * (Real.exp (8 * x) * Q) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE hQ) h.le
        _ ≤ (1 - 8 * x) * (Real.exp (8 * x) * Q) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = ((1 - 8 * x) * Real.exp (8 * x)) * Q := by ring
        _ ≤ 1 * Q := mul_le_mul_of_nonneg_right hexp1 hQ
        _ = Q := one_mul Q
  · have hy : Real.exp (8 * x) ≤ 1 + 8 * Real.exp 8 * x := by
      have h8 : Real.exp (8 * x) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by linarith)
      have : 8 * x * Real.exp (8 * x) ≤ 8 * x * Real.exp 8 :=
        mul_le_mul_of_nonneg_left h8 (by positivity)
      nlinarith
    calc ∏ s, (weylDim (m + 2) (hwt m (A s + c) (B s + c)) : ℝ)
        ≤ (1 + t) ^ K * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ) := Ph
      _ ≤ Real.exp (8 * x) * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ) :=
          mul_le_mul_of_nonneg_right hE hPh.le
      _ ≤ (1 + 8 * Real.exp 8 * x) * ∏ s, (weylDim (m + 2) (hwt m (A s) (B s)) : ℝ) :=
          mul_le_mul_of_nonneg_right hy hPh.le
end Formalism.CountingSumsFrames
