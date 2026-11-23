-- Prove2me | solution 1 for Formalism.CountingSumsFrames.binomSeries_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:43.26518+00:00
-- url     : https://prove2.me/submissions/aa63fbbb-99a0-4f28-bfb9-9cda93793eb9

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_DigitClassSize
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_BinomialSeriesBound
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_pos_real
import Theorems.Thm_Formalism_CountingSumsFrames_dimPol_succ_eq_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Filter Topology
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (k' B : ℕ) (hk : 2 ≤ k') :
    HasSum (fun j : ℕ => (dimPol k' B : ℝ) / dimPol k' (B + j)) (((B : ℝ) + k') / ((k' : ℝ) - 1)) := by
  have hk2 : (2 : ℝ) ≤ k' := by exact_mod_cast hk
  have hk1 : (0 : ℝ) < (k' : ℝ) - 1 := by linarith
  have pB := dimPol_pos_real k' B
  set g : ℕ → ℝ := fun n => (dimPol k' B : ℝ) * ((B : ℝ) + n + k') / (((k' : ℝ) - 1) * dimPol k' (B + n))
    with hg
  have hrec : ∀ n, (dimPol k' (B + (n + 1)) : ℝ)
      = dimPol k' (B + n) * ((B : ℝ) + n + 1 + k') / ((B : ℝ) + n + 1) := by
    intro n
    rw [show B + (n + 1) = B + n + 1 by omega, dimPol_succ_eq_real]
    push_cast; ring
  have hstep : ∀ n, (dimPol k' B : ℝ) / dimPol k' (B + n) = g n - g (n + 1) := by
    intro n
    have p0 := dimPol_pos_real k' (B + n)
    simp only [hg]
    rw [hrec n]
    push_cast
    field_simp
    ring
  have hsucc : ∀ n, g (n + 1) * ((B : ℝ) + n + k') = g n * ((B : ℝ) + n + 1) := by
    intro n
    have p0 := dimPol_pos_real k' (B + n)
    simp only [hg]
    rw [hrec n]
    push_cast
    field_simp
    ring
  have hg0 : ∀ n, 0 ≤ g n := by intro n; simp only [hg]; positivity
  have hgzero : g 0 = ((B : ℝ) + k') / ((k' : ℝ) - 1) := by
    simp only [hg]; simp; field_simp
  have hinv : ∀ n, g n * ((B : ℝ) + n + k' - 1) ≤ g 0 * ((B : ℝ) + k' - 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      have h1 : g (n + 1) * ((B : ℝ) + (n + 1) + k' - 1) = g n * ((B : ℝ) + n + 1) := by
        rw [← hsucc n]; ring
      rw [h1]
      have : g n * ((B : ℝ) + n + 1) ≤ g n * ((B : ℝ) + n + k' - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (hg0 n)
      linarith
  set C := g 0 * ((B : ℝ) + k' - 1) with hC
  have hbound : ∀ n, g n ≤ C * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hle : (n : ℝ) + 1 ≤ (B : ℝ) + n + k' - 1 := by
      have : (0 : ℝ) ≤ B := by positivity
      linarith
    rw [mul_one_div, le_div_iff₀ hpos]
    calc g n * ((n : ℝ) + 1) ≤ g n * ((B : ℝ) + n + k' - 1) :=
          mul_le_mul_of_nonneg_left hle (hg0 n)
      _ ≤ C := hinv n
  have htend : Tendsto g atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    rw [mul_zero] at h
    exact squeeze_zero hg0 hbound h
  have hnn : ∀ j, 0 ≤ (dimPol k' B : ℝ) / dimPol k' (B + j) := by
    intro j; have := dimPol_pos_real k' (B + j); positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hps : ∀ n, ∑ i ∈ range n, (dimPol k' B : ℝ) / dimPol k' (B + i) = g 0 - g n := by
    intro n
    rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_range_sub']
  simp_rw [hps]
  rw [← hgzero]
  have := (tendsto_const_nhds (x := g 0)).sub htend
  simpa using this
end Formalism.CountingSumsFrames
