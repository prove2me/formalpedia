-- Prove2me | solution 1 for Formalism.L2.SG.ColsDim.columns_dimension_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:17:48.658727+00:00
-- url     : https://prove2.me/submissions/e670b647-3d75-48c1-a2ef-b5ff1d29e1a7

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Theorems.Thm_Formalism_L2_SG_ColsDim_columns_dimension

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
theorem _root_.solution : ColsDimU := by
  intro F E _ _ _ _ n _ _ σ J K K0 ψ V _ _ π hK hst hfin hV
  exact columns_dimension _ _ _ ℂ V _ _ K K0 ψ π hK hst hfin hV
end Formalism.L2.SG.ColsDim
