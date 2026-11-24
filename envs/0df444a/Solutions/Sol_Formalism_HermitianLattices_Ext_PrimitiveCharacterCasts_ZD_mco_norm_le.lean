-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.mco_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:26.628803+00:00
-- url     : https://prove2.me/submissions/984399a7-5ace-4e06-b1e3-351eded8346a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZMoll
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mco_filter_subset_antidiag

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
theorem _root_.solution (Y N : ℕ) {n : ℕ} (hn : 1 ≤ n) : ‖mco Y N n‖ ≤ (n.divisors.card : ℝ) := by
  unfold mco
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (sum_le_sum (g := fun _ => (1 : ℝ)) ?_) ?_
  · intro p _
    have h1 := abs_moebius_le_one (n := p.1)
    first
      | (rw [Complex.norm_intCast]; exact_mod_cast h1)
      | (rw [Complex.norm_int]; exact_mod_cast h1)
      | (rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]; exact_mod_cast h1)
  · rw [sum_const, nsmul_eq_mul, mul_one]
    have hc := card_le_card (mco_filter_subset_antidiag (Y := Y) (N := N) hn)
    have he : n.divisorsAntidiagonal.card = n.divisors.card := by
      first
        | exact Nat.card_divisorsAntidiagonal_eq_card_divisors n
        | (rw [← Nat.map_div_right_divisors, card_map])
    rw [he] at hc
    exact_mod_cast hc
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
