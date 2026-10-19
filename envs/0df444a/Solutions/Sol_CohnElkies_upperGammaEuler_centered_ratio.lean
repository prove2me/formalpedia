-- Prove2me | solution 1 for CohnElkies.upperGammaEuler_centered_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/8ff16b84-c1b8-472c-bfc5-b5e088543a4b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaEuler_centered_cpow_ratio

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
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
  classical
  let z : ℂ := (m : ℂ) - Complex.I * (b : ℂ)
  have hncomplex : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn.ne'
  have hpow : (n : ℂ) ^ (m : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hncomplex]
    exact Complex.exp_ne_zero _
  have hfactorial : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hreal (k : ℕ) :
      (m : ℂ) + (k : ℂ) ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simp
    exact (add_pos_of_pos_of_nonneg hm
      (Nat.cast_nonneg k)).ne'
  have hcomplex (k : ℕ) :
      z + (k : ℂ) ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simp [z]
    exact (add_pos_of_pos_of_nonneg hm
      (Nat.cast_nonneg k)).ne'
  have hprodreal :
      (∏ k ∈ Finset.range (n + 1),
        ((m : ℂ) + (k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun k hk => hreal k)
  have hprodcomplex :
      (∏ k ∈ Finset.range (n + 1),
        (z + (k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun k hk => hcomplex k)
  change
    Complex.GammaSeq z n /
      Complex.GammaSeq (m : ℂ) n = _
  rw [← upperGammaEuler_centered_cpow_ratio m b hn,
    Finset.prod_div_distrib,
    Complex.GammaSeq, Complex.GammaSeq]
  change
    ((n : ℂ) ^ z * (n.factorial : ℂ) /
      (∏ k ∈ Finset.range (n + 1), (z + (k : ℂ)))) /
        ((n : ℂ) ^ (m : ℂ) * (n.factorial : ℂ) /
          (∏ k ∈ Finset.range (n + 1),
            ((m : ℂ) + (k : ℂ)))) =
      ((n : ℂ) ^ z / (n : ℂ) ^ (m : ℂ)) *
        ((∏ k ∈ Finset.range (n + 1),
          ((m : ℂ) + (k : ℂ))) /
          (∏ k ∈ Finset.range (n + 1),
            (z + (k : ℂ))))
  field_simp [hpow, hfactorial, hprodreal, hprodcomplex]
end CohnElkies
