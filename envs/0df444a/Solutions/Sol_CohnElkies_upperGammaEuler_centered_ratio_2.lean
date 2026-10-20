-- Prove2me | solution 2 for CohnElkies.upperGammaEuler_centered_ratio
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:34:29.19524+00:00
-- url     : https://prove2.me/submissions/6e6bd054-ed98-4943-a8b7-0f528428d62b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    {m : ℝ} (hm : 0 < m) (b : ℝ)
    {n : ℕ} (hn : 0 < n) :
    Complex.GammaSeq
        ((m : ℂ) - Complex.I * (b : ℂ)) n /
      Complex.GammaSeq (m : ℂ) n =
      Complex.exp
        (-Complex.I *
          ((b * Real.log (n : ℝ) : ℝ) : ℂ)) *
        ∏ k ∈ Finset.range (n + 1),
          (((m : ℂ) + (k : ℂ)) /
            ((m : ℂ) - Complex.I * (b : ℂ) + (k : ℂ))) := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hP1 : ∏ k ∈ Finset.range (n + 1), ((m:ℂ) + (k:ℂ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k _ h
    have := congrArg Complex.re h
    simp at this
    linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hP2 : ∏ k ∈ Finset.range (n + 1), ((m:ℂ) - Complex.I * (b:ℂ) + (k:ℂ)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k _ h
    have := congrArg Complex.re h
    simp at this
    linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hcm : (n:ℂ) ^ (m:ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn0]; exact Complex.exp_ne_zero _
  have hf : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hcp : (n:ℂ) ^ ((m:ℂ) - Complex.I * (b:ℂ)) =
      (n:ℂ) ^ (m:ℂ) * Complex.exp (-Complex.I * ((b * Real.log (n:ℝ) : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_add]
    congr 1
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    push_cast
    ring
  unfold Complex.GammaSeq
  rw [Finset.prod_div_distrib, hcp]
  field_simp

