-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.discriminant_real_subfield
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:10.082129+00:00
-- url     : https://prove2.me/submissions/ae1fec0e-7b55-4ac5-9ca5-4deaf6d5a344

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
import Theorems.Thm_Formalism_FrobeniusOrbits_Discr_discr_F

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Discr
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : DiscrMaximalRealCyclotomic := by
  intro e L _ _ ζ hζ
  have hne : NeZero (2 ^ (e + 2)) := ⟨by positivity⟩
  have hcyc : IsCyclotomicExtension {2 ^ (e + 2)} ℚ ℚ⟮ζ⟯ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hz : IsPrimitiveRoot (AdjoinSimple.gen ℚ ζ) (2 ^ (e + 2)) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ
  rw [← NumberField.discr_eq_discr_of_ringEquiv _ (equivF ζ)]
  exact discr_F hz
end Formalism.FrobeniusOrbits
