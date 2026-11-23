-- Prove2me | solution 1 for Formalism.L2.SG.ColsDim.columns_dimension
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:34.940802+00:00
-- url     : https://prove2.me/submissions/78391b5e-7fc3-4953-814e-2b9e27abab0a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Theorems.Thm_Formalism_L2_SG_ColsDim_stabTriv_mono
import Theorems.Thm_Formalism_L2_SG_ColsDim_equi_dim

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
theorem _root_.solution : ColsDim := by
  intro Γ Gi Gf _ _ _ k _ V _ _ ιi ιf K K0 ψ π hK hst hfin hV
  obtain ⟨h1, h2⟩ := equi_dim ιf K (stabTriv_mono ιf hK hst) (dualRep ιi π) ψ
  let e := colsEquiv ιf K ιi ψ π
  haveI := h1
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [e.finrank_eq, h2, Subspace.dual_finrank_eq]
end Formalism.L2.SG.ColsDim
