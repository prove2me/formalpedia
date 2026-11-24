-- Prove2me | solution 1 for Formalism.HF.P.hasDerivAt_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:20.380497+00:00
-- url     : https://prove2.me/submissions/46a13d7c-d8d3-41af-932c-ce7156315012

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir
import Theorems.Thm_Formalism_HF_P_log_div_rpow_nonneg
import Theorems.Thm_Formalism_HF_P_summable_log_div_rpow
import Theorems.Thm_Formalism_HF_P_hasDerivAt_term
import Theorems.Thm_Formalism_HF_P_summable_F

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
theorem _root_.solution (S : Set ℕ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x : ℝ => ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator
        (fun m : ℕ => 1 / (m : ℝ) ^ x) n)
      (-∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n)
      x := by
  set y := (1 + x) / 2 with hy
  have hy1 : 1 < y := by rw [hy]; linarith
  have hyx : y < x := by rw [hy]; linarith
  rw [← tsum_neg]
  refine hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => Real.log n / (n : ℝ) ^ y)
    (g := fun n z => {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => 1 / (m : ℝ) ^ z) n)
    (g' := fun n z => -{p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ z) n)
    (summable_log_div_rpow hy1) isOpen_Ioi isPreconnected_Ioi
    (fun n z _ => hasDerivAt_term S n z) (fun n z hz => ?_) (mem_Ioi.2 hyx) ?_ (mem_Ioi.2 hyx)
  · have hz' : y < z := mem_Ioi.1 hz
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (Set.indicator_nonneg (fun m _ => log_div_rpow_nonneg m z) n)]
    refine (Set.indicator_le_self' (fun m _ => log_div_rpow_nonneg m z) n).trans ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn1 : (1:ℝ) ≤ n := Nat.one_le_cast.2 hn
      have hpos : 0 < (n:ℝ) ^ y := Real.rpow_pos_of_pos (by linarith) y
      exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg n) hpos
        (Real.rpow_le_rpow_of_exponent_le hn1 hz'.le)
  · exact summable_F S (by linarith)
end Formalism.HF.P
