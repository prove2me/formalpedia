-- Prove2me | solution 1 for Formalism.L2.DIV.fockL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:48.406892+00:00
-- url     : https://prove2.me/submissions/fa1c69cb-2466-4ccd-a443-69e1dc8cdcaf

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [StarRing K] {σ : Type}
namespace Formalism.L2.DIV
theorem _root_.solution (f g : MvPolynomial σ K) : fockL f g = fockS f g := rfl
end Formalism.L2.DIV
