-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.massTelescope_form_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:01.154812+00:00
-- url     : https://prove2.me/submissions/b5885fe9-2df2-43a8-b3ea-4acd0b445991

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassTelescope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (n : ℕ) (x y : Fin n → K) :
    massTelescope_form K n x y = ∑ i, star (x i) * y i := rfl
end Formalism.HermitianLatticesTheory
