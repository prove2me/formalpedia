-- Prove2me | solution 1 for Formalism.ELL.FormalGroupQuadraticJets.cc_omega
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:43.115464+00:00
-- url     : https://prove2.me/submissions/74f134a0-fe26-49d6-8fdd-476b4afd7268

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupQuadraticJets
open Formalism.G.LogCR
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.ELL.FormalGroupQuadraticJets
theorem _root_.solution (F : FormalGroup (Formalism.G.unitBall K)) :
    PowerSeries.constantCoeff (omegaF F) = ccd 1 (FK F).toPowerSeries := by
  unfold Formalism.ELL.omegaF
  exact Formalism.G.LogP.constantCoeff_subst_of_zero _ hb
end Formalism.ELL.FormalGroupQuadraticJets
