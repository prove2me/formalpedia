-- Prove2me | solution 1 for Egrs75.MathlibAPI.irrational_log_div_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:25:45.494963+00:00
-- url     : https://prove2.me/submissions/3ba387bd-28c5-45a5-beda-49e467f8c03d

module
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Definitions.Def_LeanPool_Egrs75_LogIrrationality
public import Theorems.Thm_Egrs75_MathlibAPI_no_pow_eq

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MathlibAPI
open Nat
open Egrs75
namespace Egrs75.MathlibAPI
theorem _root_.solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : Irrational (Real.log p / Real.log q) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hlq : 0 < Real.log q := Real.log_pos hq1
  rw [irrational_iff_ne_rational]
  intro a b hb heq
  -- heq : log p / log q = a / b.  Cross-multiply: b * log p = a * log q.
  have hcross : (b : ℝ) * Real.log p = (a : ℝ) * Real.log q := by
    field_simp at heq
    linarith [heq]
  -- log p / log q > 0 and = a/b ⟹ a, b same sign. Normalise to positive naturals.
  have hpos : 0 < Real.log p / Real.log q := div_pos hlp hlq
  rw [heq] at hpos
  -- a/b > 0 with b ≠ 0 ⟹ a ≠ 0 and a, b same sign.
  -- Set n = |b| ≥ 1, m = |a| ≥ 1, with n * log p = m * log q.
  have hane : (a : ℝ) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hpos; exact lt_irrefl _ hpos
  have ha0 : a ≠ 0 := by exact_mod_cast hane
  set n := b.natAbs with hn_def
  set m := a.natAbs with hm_def
  have hn1 : 1 ≤ n := by
    rw [hn_def]; exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hb)
  have hm1 : 1 ≤ m := by
    rw [hm_def]; exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr ha0)
  -- From b*log p = a*log q derive n*log p = m*log q (absolute values, same sign).
  have hnm : (n : ℝ) * Real.log p = (m : ℝ) * Real.log q := by
    -- a/b > 0 ⟹ sign a = sign b. Use |b|*log p = |a|*log q from hcross via signs.
    -- Multiply hcross through by sign; easier: take absolute values using positivity.
    -- |b * log p| = |a * log q|, and log p, log q > 0.
    have habs : |(b : ℝ)| * Real.log p = |(a : ℝ)| * Real.log q := by
      have h1 : |(b : ℝ) * Real.log p| = |(a : ℝ) * Real.log q| := by rw [hcross]
      rwa [abs_mul, abs_mul, abs_of_pos hlp, abs_of_pos hlq] at h1
    simp_all
  -- n * log p = log (p^n), m * log q = log (q^m).
  have hlogp : Real.log ((p : ℝ) ^ n) = (n : ℝ) * Real.log p := Real.log_pow _ _
  have hlogq : Real.log ((q : ℝ) ^ m) = (m : ℝ) * Real.log q := Real.log_pow _ _
  have hlogeq : Real.log ((p : ℝ) ^ n) = Real.log ((q : ℝ) ^ m) := by
    rw [hlogp, hlogq]; exact hnm
  -- log injective on (0,∞): p^n, q^m > 0 ⟹ p^n = q^m.
  have hppos : (0 : ℝ) < (p : ℝ) ^ n := pow_pos (by linarith) n
  have hqpos : (0 : ℝ) < (q : ℝ) ^ m := pow_pos (by linarith) m
  have hpoweq : (p : ℝ) ^ n = (q : ℝ) ^ m :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr hppos) (Set.mem_Ioi.mpr hqpos) hlogeq
  exact no_pow_eq hp hq hpq hn1 hpoweq
end Egrs75.MathlibAPI
