-- Prove2me | solution 1 for Formalism.MainNotions.UnusedSlot33.HK.isGalK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:35:09.720797+00:00
-- url     : https://prove2.me/submissions/92c412bf-b0bd-4dcc-afa8-b88a2489cddb

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.UnusedSlot33 Formalism.MainNotions.UnusedSlot33.HK
open NumberField Polynomial Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
variable {R : Ranks} (H : Host R)
namespace Formalism.MainNotions.UnusedSlot33.HK
theorem _root_.solution : IsGalois ℚ H.K := by
  haveI : IsGalois ℚ H.E := H.galois
  haveI hn : (IntermediateField.fixingSubgroup H.K).Normal := by
    constructor
    intro n hn g
    have hc : g * n * g⁻¹ = n := H.gal.injective (by
      rw [map_mul, map_mul, map_inv, mul_comm (H.gal g) (H.gal n), mul_inv_cancel_right])
    rw [hc]
    exact hn
  have h1 := IsGalois.of_fixedField_normal_subgroup (IntermediateField.fixingSubgroup H.K)
  rw [IsGalois.fixedField_fixingSubgroup] at h1
  exact h1
end Formalism.MainNotions.UnusedSlot33.HK
