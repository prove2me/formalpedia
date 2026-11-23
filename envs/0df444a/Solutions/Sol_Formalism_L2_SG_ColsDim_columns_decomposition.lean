-- Prove2me | solution 1 for Formalism.L2.SG.ColsDim.columns_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:35.271697+00:00
-- url     : https://prove2.me/submissions/321a4f6b-68a6-4bb0-a3d4-d651ea889824

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.ColsDim
open Formalism.UG
namespace Formalism.L2.SG.ColsDim
theorem _root_.solution : ColsDecomp := by
  intro Γ Gi Gf _ _ _ k _ V _ _ ιi ιf K ψ π s hs hst
  exact ⟨(colsEquiv ιf K ιi ψ π).trans (decEquiv ιf K hst s hs (dualRep ιi π) ψ), fun T c ξ => rfl⟩
end Formalism.L2.SG.ColsDim
