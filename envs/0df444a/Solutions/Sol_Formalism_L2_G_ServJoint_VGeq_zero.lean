-- Prove2me | solution 1 for Formalism.L2.G.ServJoint.VGeq.zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:04.182634+00:00
-- url     : https://prove2.me/submissions/64f746c9-4c22-446f-810c-2b70ef522a6c

import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_NormaliserValuationBound
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_JointServices_VAddEqVw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions (vAdd)
open Formalism.DivisionValues (vw)
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.ServJoint
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.G.ServJoint
namespace VGeq
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : VGeq w s (0 : K) := Or.inl rfl
end VGeq
end Formalism.L2.G.ServJoint
