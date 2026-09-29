-- Prove2me | solution 1 for Freiman.trunk_diagonal_denominators
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-12T04:22:06.554452+00:00
-- url     : https://prove2.me/submissions/3f46cec1-c20d-4037-8a60-269f62375711

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

theorem den_pos (t : CertThreshold) (r : ℝ) (hr : 0 ≤ r) (h0 : 0 ≤ certFieldVal t.x0)
    (h1 : 0 ≤ certFieldVal t.x1) : 0 < certThresholdDen t r := by
  unfold certThresholdDen
  exact mul_pos (by nlinarith [mul_nonneg hr h0]) (by nlinarith [mul_nonneg hr h1])

theorem solution (C : TrunkCatalog) (w : TrunkWitness) (hw : trunkWitnessValid C w) (hn : w.diagonal ≠ 0)
    (r s : ℝ) (hm : certRectangleMem w.rectangle r s) :
    0 < certThresholdDen (trunkBound C w.lowerId).threshold r ∧ 0 < certThresholdDen (trunkBound C w.upperId).threshold r := by
  unfold trunkWitnessValid at hw
  obtain ⟨-, -, -, -, h⟩ := hw
  rw [if_neg hn] at h
  obtain ⟨-, -, hr0, -, -, hv1, hv2, -⟩ := h
  obtain ⟨m1, -, -, -⟩ := hm
  have hr : 0 ≤ r := le_trans (by exact_mod_cast hr0) m1
  have v1 : 0 ≤ certFieldVal (trunkBound C w.lowerId).threshold.x0 ∧
      0 ≤ certFieldVal (trunkBound C w.lowerId).threshold.x1 :=
    ⟨le_trans (by exact_mod_cast hv1.1) (lower_le _), le_trans (by exact_mod_cast hv1.2) (lower_le _)⟩
  have v2 : 0 ≤ certFieldVal (trunkBound C w.upperId).threshold.x0 ∧
      0 ≤ certFieldVal (trunkBound C w.upperId).threshold.x1 :=
    ⟨le_trans (by exact_mod_cast hv2.1) (lower_le _), le_trans (by exact_mod_cast hv2.2) (lower_le _)⟩
  exact ⟨den_pos _ r hr v1.1 v1.2, den_pos _ r hr v2.1 v2.2⟩
