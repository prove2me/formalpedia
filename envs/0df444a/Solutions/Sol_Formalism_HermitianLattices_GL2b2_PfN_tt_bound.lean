-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2b2.PfN.tt_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:44:49.90285+00:00
-- url     : https://prove2.me/submissions/a15cf015-d423-4441-ae6c-9323bcea467e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_cpow_diff_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2b2
open Formalism.HermitianLattices.GL2b2.PfN
open Complex
namespace Formalism.HermitianLattices.GL2b2.PfN
theorem _root_.solution (k : ℕ) (s : ℂ) (δ R : ℝ) (hδ : 0 < δ) (h1 : δ ≤ s.re) (h2 : ‖s‖ ≤ R) :
    ‖tt k s‖ ≤ 4 * R * ((k : ℝ) + 1) ^ (-1 - δ) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have aux : ∀ c : ℝ, 1 ≤ c → (8 * (k : ℝ) + c) ^ (-s.re - 1) ≤ ((k : ℝ) + 1) ^ (-1 - δ) := by
    intro c hc
    calc (8 * (k : ℝ) + c) ^ (-s.re - 1) ≤ ((k : ℝ) + 1) ^ (-s.re - 1) :=
          Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith) (Set.mem_Ioi.2 (by linarith))
            (Set.mem_Ioi.2 (by linarith)) (by linarith)
      _ ≤ ((k : ℝ) + 1) ^ (-1 - δ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have b1 := cpow_diff_bound s (by linarith) (8 * (k : ℝ) + 1) (8 * (k : ℝ) + 3) (by linarith) (by linarith)
  have b2 := cpow_diff_bound s (by linarith) (8 * (k : ℝ) + 5) (8 * (k : ℝ) + 7) (by linarith) (by linarith)
  have hP : 0 ≤ ((k : ℝ) + 1) ^ (-1 - δ) := Real.rpow_nonneg (by linarith) _
  have hR : 0 ≤ R := le_trans (norm_nonneg _) h2
  have c1 : ‖s‖ * (8 * (k : ℝ) + 1) ^ (-s.re - 1) ≤ R * ((k : ℝ) + 1) ^ (-1 - δ) :=
    mul_le_mul h2 (aux 1 le_rfl) (Real.rpow_nonneg (by linarith) _) hR
  have c2 : ‖s‖ * (8 * (k : ℝ) + 5) ^ (-s.re - 1) ≤ R * ((k : ℝ) + 1) ^ (-1 - δ) :=
    mul_le_mul h2 (aux 5 (by norm_num)) (Real.rpow_nonneg (by linarith) _) hR
  have e : tt k s = -(((8 * (k : ℝ) + 3 : ℝ) : ℂ) ^ (-s) - ((8 * (k : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) +
      (((8 * (k : ℝ) + 7 : ℝ) : ℂ) ^ (-s) - ((8 * (k : ℝ) + 5 : ℝ) : ℂ) ^ (-s)) := by
    unfold tt; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]
  have d1 : (8 * (k : ℝ) + 3) - (8 * (k : ℝ) + 1) = 2 := by ring
  have d2 : (8 * (k : ℝ) + 7) - (8 * (k : ℝ) + 5) = 2 := by ring
  rw [d1] at b1
  rw [d2] at b2
  linarith
end Formalism.HermitianLattices.GL2b2.PfN
