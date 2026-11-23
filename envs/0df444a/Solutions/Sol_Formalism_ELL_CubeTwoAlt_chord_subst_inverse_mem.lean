-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.chord_subst_inverse_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:03.42886+00:00
-- url     : https://prove2.me/submissions/7985c92c-e727-47eb-aaf1-17ba5d7d2080

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_vec_mem
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_subst_mem_T_of_mem
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_ib_cc
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_inverseSeries_subst_X1_mem
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_X_mem_T
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_formalSum_mem_integralSeries


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeTwoAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K] {W : WeierstrassCurve K} {w : PowerSeries K}
local notation "cc" => MvPowerSeries.constantCoeff
namespace Formalism.ELL.CubeTwoAlt
theorem _root_.solution (hw : WFixed W w) :
    (WeierstrassChordSeries.F2 W w).subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] ∈ T W :=
  subst_mem_T_of_mem (formalSum_mem_integralSeries hw) (vec_mem (X_mem_T 0) (inverseSeries_subst_X1_mem hw))
    (FormalGroupQuadraticJets.hv (by simp) (ib_cc hw))
end Formalism.ELL.CubeTwoAlt
