-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mco_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:09.045461+00:00
-- url     : https://prove2.me/submissions/ce0b4d38-8976-4b8e-ba19-8e69e2d65baa

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZMoll
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mco_filter_eq_antidiag
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mco_sum_moebius_divisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution {Y N n : ℕ} (h2 : 2 ≤ n) (hnY : n ≤ Y) (hYN : Y ≤ N) : mco Y N n = 0 := by
  unfold mco
  rw [mco_filter_eq_antidiag (by omega) hnY hYN]
  have h := Nat.sum_divisorsAntidiagonal (fun a _ => ((μ a : ℤ) : ℂ)) (n := n)
  rw [h]
  exact_mod_cast mco_sum_moebius_divisors h2
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
