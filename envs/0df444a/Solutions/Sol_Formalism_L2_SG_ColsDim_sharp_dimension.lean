-- Prove2me | solution 1 for Formalism.L2.SG.ColsDim.sharp_dimension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:54.931678+00:00
-- url     : https://prove2.me/submissions/54256f2d-cd36-4382-897c-6641a5e3c0ac

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
theorem _root_.solution : SharpDim := by
  intro Γ Gi Gf _ _ _ k _ V _ _ ιi ιf K K0 ψ π hK hst hfin hV
  exact equi_dim ιf K (stabTriv_mono ιf hK hst) (π.comp ιi) ψ⁻¹
end Formalism.L2.SG.ColsDim
