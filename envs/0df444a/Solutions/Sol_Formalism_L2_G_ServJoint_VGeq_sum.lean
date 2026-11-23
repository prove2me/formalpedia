-- Prove2me | solution 1 for Formalism.L2.G.ServJoint.VGeq.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:56:34.355072+00:00
-- url     : https://prove2.me/submissions/c98c19d5-9acb-497b-b27a-d0a151c76008

import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_NormaliserValuationBound
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_JointServices_VAddEqVw
import Theorems.Thm_Formalism_L2_G_ServJoint_VGeq_zero
import Theorems.Thm_Formalism_L2_G_ServJoint_VGeq_add

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
theorem _root_.solution {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {ι : Type*} (S : Finset ι) (f : ι → K)
    (h : ∀ i ∈ S, VGeq w s (f i)) : VGeq w s (∑ i ∈ S, f i) := by
  exact Finset.sum_induction f (VGeq w s) (fun a b ha hb => ha.add hb) (VGeq.zero w s) h
end VGeq
end Formalism.L2.G.ServJoint
