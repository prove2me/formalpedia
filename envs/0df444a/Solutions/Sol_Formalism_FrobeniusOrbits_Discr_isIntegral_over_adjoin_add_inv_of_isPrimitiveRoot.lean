-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.isIntegral_over_adjoin_add_inv_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:00.097797+00:00
-- url     : https://prove2.me/submissions/54b911a5-ec8d-4240-8439-0a127775bde1

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield

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
open Formalism.FrobeniusOrbits.Discr
variable {K : Type*} [Field K] [NumberField K] {e : ℕ} {z : K}
namespace Formalism.FrobeniusOrbits.Discr
theorem _root_.solution (hz : IsPrimitiveRoot z (2 ^ (e + 2))) : IsIntegral ℚ⟮z + z⁻¹⟯ z :=
  (Algebra.IsIntegral.isIntegral (R := ℚ) z).tower_top
end Formalism.FrobeniusOrbits.Discr
