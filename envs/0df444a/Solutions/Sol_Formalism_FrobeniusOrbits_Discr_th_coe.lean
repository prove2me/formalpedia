-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Discr.th_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:00.143323+00:00
-- url     : https://prove2.me/submissions/f5a1c86c-a5a5-40f8-a9ff-dfc991ab1239

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
theorem _root_.solution (z : K) : ((th z : ℚ⟮z + z⁻¹⟯) : K) = z + z⁻¹ := rfl
end Formalism.FrobeniusOrbits.Discr
