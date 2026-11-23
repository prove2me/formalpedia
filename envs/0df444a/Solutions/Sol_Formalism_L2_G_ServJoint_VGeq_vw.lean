-- Prove2me | solution 1 for Formalism.L2.G.ServJoint.VGeq.vw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:28.733803+00:00
-- url     : https://prove2.me/submissions/7a6bc1b1-8913-41f9-9082-dca5867d3bc9

import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalToGlobal_ExponentGrids_ExponentGridsProofs_NormaliserValuationBound
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_JointServices_VAddEqVw
import Theorems.Thm_Formalism_L2_G_ServJoint_vAdd_eq_vw

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
theorem _root_.solution {w : HeightOneSpectrum (𝓞 K)} {s : ℝ} {z : K} (h : VGeq w s z) : z = 0 ∨ s ≤ (Formalism.DivisionValues.vw w z : ℝ) := by
  by_cases hz : z = 0
  · exact Or.inl hz
  rcases h with h | h
  · exact Or.inl h
  right
  rw [← vAdd_eq_vw w z hz]
  exact h
end VGeq
end Formalism.L2.G.ServJoint
