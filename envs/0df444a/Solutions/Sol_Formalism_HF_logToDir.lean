-- Prove2me | solution 1 for Formalism.HF.logToDir
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:00.390812+00:00
-- url     : https://prove2.me/submissions/ae3b6496-7ce8-4243-88cb-18b42aea0b6b

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir
import Theorems.Thm_Formalism_HF_P_dirichlet_density_of_log_density

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.HF
namespace Formalism.HF
theorem _root_.solution : LogToDir := fun S δ h => Formalism.HF.P.dirichlet_density_of_log_density S δ h
end Formalism.HF
