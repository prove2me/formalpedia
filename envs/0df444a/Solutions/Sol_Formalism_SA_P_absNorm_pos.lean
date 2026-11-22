-- Prove2me | solution 1 for Formalism.SA.P.absNorm_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:14.851946+00:00
-- url     : https://prove2.me/submissions/372d45ac-6cbf-4551-ae4f-9eaea9dd01d8

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_SqrtAbsNormLeProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open NumberField Finset
variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
namespace Formalism.SA.P
theorem _root_.solution (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0) :
    (0 : ℝ) < (FractionalIdeal.absNorm b : ℝ) := by
  have h : FractionalIdeal.absNorm b * FractionalIdeal.absNorm b⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hb, map_one]
  have h0 := FractionalIdeal.absNorm_nonneg b
  have hq : (0 : ℚ) < FractionalIdeal.absNorm b := by
    refine lt_of_le_of_ne h0 ?_
    intro h'
    rw [← h', zero_mul] at h
    exact zero_ne_one h
  exact_mod_cast hq
end Formalism.SA.P
