-- Prove2me | solution 1 for Formalism.HF.P.hasDerivAt_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:59.439449+00:00
-- url     : https://prove2.me/submissions/a988cdb3-5056-463a-b2d3-55e3dd61b188

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution (S : Set ℕ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => 1 / (m : ℝ) ^ x) n)
      (-{p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) x := by
  by_cases h : n ∈ {p : ℕ | p.Prime ∧ p ∈ S}
  · simp only [Set.indicator_of_mem h]
    have hn : (0:ℝ) < n := Nat.cast_pos.2 h.1.pos
    have h1 := (Real.hasStrictDerivAt_const_rpow hn x).hasDerivAt
    have h2 := h1.inv (Real.rpow_pos_of_pos hn x).ne'
    have hfun : (fun x : ℝ => 1 / (n:ℝ) ^ x) = fun x => ((n:ℝ) ^ x)⁻¹ := by
      funext z; exact one_div _
    have h3 : HasDerivAt (fun x : ℝ => ((n:ℝ) ^ x)⁻¹) (-((n:ℝ) ^ x * Real.log n) / ((n:ℝ) ^ x) ^ 2) x := h2
    rw [hfun]
    refine h3.congr_deriv ?_
    have : 0 < (n:ℝ) ^ x := Real.rpow_pos_of_pos hn x
    rw [neg_div, pow_two, mul_div_mul_left _ _ this.ne']
  · simp only [Set.indicator_of_notMem h, neg_zero]
    exact hasDerivAt_const x 0
end Formalism.HF.P
