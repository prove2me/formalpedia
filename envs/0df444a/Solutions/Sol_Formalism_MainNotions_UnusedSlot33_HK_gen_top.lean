-- Prove2me | solution 1 for Formalism.MainNotions.UnusedSlot33.HK.gen_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:34:01.823211+00:00
-- url     : https://prove2.me/submissions/d1db149f-5057-4121-a669-33ddd9b36a2c

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
theorem _root_.solution (H : Host R) (x : H.K) (hx : (x : H.E) = H.sqd) :
    IntermediateField.adjoin ℚ {x} = ⊤ := by
  apply IntermediateField.map_injective (IsScalarTower.toAlgHom ℚ H.K H.E)
  rw [IntermediateField.adjoin_map, Set.image_singleton]
  first
  | rw [IntermediateField.map_top]
  | rw [← AlgHom.fieldRange_eq_map]
  ext z
  rw [AlgHom.mem_fieldRange]
  have h1 : IsScalarTower.toAlgHom ℚ H.K H.E x = H.sqd := hx
  rw [h1]
  constructor
  · intro hz
    exact ⟨⟨z, hz⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2
end Formalism.MainNotions.UnusedSlot33.HK
