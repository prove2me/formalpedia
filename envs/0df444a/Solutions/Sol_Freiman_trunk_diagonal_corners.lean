-- Prove2me | solution 1 for Freiman.trunk_diagonal_corners
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T07:53:36.150398+00:00
-- url     : https://prove2.me/submissions/ee9fcaa0-269a-408b-9e6e-889b5af9fb92

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem sqrt_bracket (n l u : ℝ) (hl : 0 ≤ l) (hu : 0 ≤ u) (hln : l^2 < n) (hnu : n < u^2) :
    l < Real.sqrt n ∧ Real.sqrt n < u := by
  have hn : 0 ≤ n := le_trans (sq_nonneg l) hln.le
  have hs := Real.sqrt_nonneg n
  have he := Real.sq_sqrt hn
  constructor <;> nlinarith

theorem br3 : (certSqrt3Lower:ℝ) ≤ Real.sqrt 3 ∧ Real.sqrt 3 ≤ certSqrt3Upper := by
  unfold certSqrt3Lower certSqrt3Upper
  push_cast
  have := sqrt_bracket 3 (1732050807568877293527446341505 / 10^30) (1732050807568877293527446341506 / 10^30)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨this.1.le, this.2.le⟩
theorem br7 : (certSqrt7Lower:ℝ) ≤ Real.sqrt 7 ∧ Real.sqrt 7 ≤ certSqrt7Upper := by
  unfold certSqrt7Lower certSqrt7Upper
  push_cast
  have := sqrt_bracket 7 (2645751311064590590501615753639 / 10^30) (2645751311064590590501615753640 / 10^30)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨this.1.le, this.2.le⟩
theorem br21 : (certSqrt21Lower:ℝ) ≤ Real.sqrt 21 ∧ Real.sqrt 21 ≤ certSqrt21Upper := by
  unfold certSqrt21Lower certSqrt21Upper
  push_cast
  have := sqrt_bracket 21 (4582575694955840006588047193728 / 10^30) (4582575694955840006588047193729 / 10^30)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨this.1.le, this.2.le⟩

theorem directed (q lo hi : ℚ) (x : ℝ) (hlo : (lo:ℝ) ≤ x) (hhi : x ≤ hi) :
    (certDirectedTerm q lo hi : ℝ) ≤ (q:ℝ)*x := by
  unfold certDirectedTerm
  split_ifs with h
  · push_cast
    exact mul_le_mul_of_nonneg_left hlo (by exact_mod_cast h)
  · push_cast
    exact mul_le_mul_of_nonpos_left hhi (by exact_mod_cast (le_of_lt (lt_of_not_ge h)))

theorem lower_le (z : CertField) : (certFieldLower z : ℝ) ≤ certFieldVal z := by
  unfold certFieldLower certFieldVal
  have h3 := directed z.b certSqrt3Lower certSqrt3Upper (Real.sqrt 3) br3.1 br3.2
  have h7 := directed z.c certSqrt7Lower certSqrt7Upper (Real.sqrt 7) br7.1 br7.2
  have h21 := directed z.d certSqrt21Lower certSqrt21Upper (Real.sqrt 21) br21.1 br21.2
  push_cast
  linarith

theorem solution (C : TrunkCatalog) (w : TrunkWitness)
    (hw : trunkWitnessValid C w) (hn : w.diagonal ≠ 0) :
    ∀ i j : Fin 2, 0 < (w.diagonal : ℝ)*(certFieldVal (trunkPolynomial C w 1 0)+
    certFieldVal (trunkPolynomial C w 2 0)*((trunkCorner w.rectangle.r0 w.rectangle.r1 i : ℝ)+trunkCorner w.rectangle.s0 w.rectangle.s1 j)+
    certFieldVal (trunkPolynomial C w 2 1)*trunkCorner w.rectangle.r0 w.rectangle.r1 i*trunkCorner w.rectangle.s0 w.rectangle.s1 j) := by
  intro i j
  obtain ⟨-, -, -, -, hrest⟩ := hw
  rw [if_neg hn] at hrest
  obtain ⟨-, -, -, -, -, -, -, -, -, hmargin, hcoef⟩ := hrest
  have h1 := hcoef i j
  have h2 := lower_le (trunkDiagonalCoefficient C w i j)
  have hval : certFieldVal (trunkDiagonalCoefficient C w i j) =
      (w.diagonal : ℝ)*(certFieldVal (trunkPolynomial C w 1 0)+
      certFieldVal (trunkPolynomial C w 2 0)*((trunkCorner w.rectangle.r0 w.rectangle.r1 i : ℝ)+trunkCorner w.rectangle.s0 w.rectangle.s1 j)+
      certFieldVal (trunkPolynomial C w 2 1)*trunkCorner w.rectangle.r0 w.rectangle.r1 i*trunkCorner w.rectangle.s0 w.rectangle.s1 j) := by
    unfold trunkDiagonalCoefficient certFieldScale certFieldAdd certFieldVal
    push_cast
    ring
  rw [hval] at h2
  have h3 : (0:ℝ) < ((w.margin / 2 : ℚ) : ℝ) := by
    have : (0:ℚ) < w.margin/2 := by linarith
    exact_mod_cast this
  have h4 : ((w.margin/2 : ℚ) : ℝ) < (certFieldLower (trunkDiagonalCoefficient C w i j) : ℝ) := by
    exact_mod_cast h1
  linarith
