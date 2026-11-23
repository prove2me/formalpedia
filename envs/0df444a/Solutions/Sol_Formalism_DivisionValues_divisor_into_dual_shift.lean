-- Prove2me | solution 1 for Formalism.DivisionValues.divisor_into_dual_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:37.377193+00:00
-- url     : https://prove2.me/submissions/68f08dd4-5103-43a0-9da8-718a62b397f8

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
import Theorems.Thm_Formalism_DivisionValues_shift_pairing_formula
import Theorems.Thm_Formalism_DivisionValues_divisor_into_dual_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : DivIntoDualShift := by
  intro K _ _ _ d D R B n M π ι P ζ hζ0 hζ hP N N' σ τ hσ hτ hsh hR φ hφ
  refine divisor_into_dual_lattice K D R (B φ) n M π ι (fun w => P w φ) ζ hζ0 hζ (fun w F => hP w φ F)
    ?_ hR
  intro w F hF
  refine shift_pairing_formula K d w N N' (τ w) (hsh w) ((P w).flip F) ?_ φ hφ
  intro φ0 hφ0
  rcases hσ w φ0 hφ0 F hF with h | h
  · exact Or.inl h
  · right
    exact le_trans (hτ w) (Int.ceil_le.mpr h)
end Formalism.DivisionValues
