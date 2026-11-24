-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.inv_sfac_le_vsph
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:46.638001+00:00
-- url     : https://prove2.me/submissions/03423163-0ff0-4f6b-82bb-e4d12f7069fd

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_vsph_add
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_two_pi_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (k : ℕ) : (sfac k)⁻¹ ≤ Vsph k := by
  have h := vsph_add 0 k
  have h0 : Vsph 0 = 1 := by simp [Vsph]
  rw [zero_add, h0, one_mul] at h
  rw [h]
  unfold sfac
  rw [← Finset.prod_inv_distrib]
  apply Finset.prod_le_prod (fun i _ => by positivity)
  intro i _
  rw [zero_add, div_eq_mul_inv]
  have := one_le_two_pi_pow (i + 1)
  have h2 : (0:ℝ) ≤ ((i.factorial : ℝ))⁻¹ := by positivity
  nlinarith
end Formalism.HermitianLatticeCounting.P
