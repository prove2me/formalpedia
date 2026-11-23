-- Prove2me | solution 1 for Formalism.L2.Th1.H.exp_neg_le_factorial_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:49.774255+00:00
-- url     : https://prove2.me/submissions/56ff9ecf-ad2a-4bd3-9957-69dca741b74c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {s : ℝ} (hs : 0 < s) (n : ℕ) : Real.exp (-s) ≤ (n ! : ℝ) / s ^ n := by
  have h1 : s ^ n / (n ! : ℝ) ≤ Real.exp s := Real.pow_div_factorial_le_exp s hs.le n
  have hf : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have hp : 0 < s ^ n := pow_pos hs n
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos s) hp]
  rw [div_le_iff₀ hf] at h1
  linarith
end Formalism.L2.Th1.H
