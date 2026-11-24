-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.Fp_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:24.0449+00:00
-- url     : https://prove2.me/submissions/c83d689d-1a31-4606-82ca-49637efc413b

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_dI_cc
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_invSer_subst
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_ib_cc
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_ccd_F
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_ccd_single
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_L_X
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_L_mul
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_linearCoeff_formalSum


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
    MvPowerSeries.coeff (Finsupp.single 1 1) ((WeierstrassChordSeries.F2 W w).subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)]) = -1 := by
  have h := FormalGroupQuadraticJets.ccd_F (WeierstrassChordSeries.F2 W w) (x := (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
    (by simp) (ib_cc hw) 1
  simp only [FormalGroupQuadraticJets.ccd_single] at h
  rw [h, linearCoeff_formalSum hw 0, linearCoeff_formalSum hw 1, invSer_subst hw 1, WeierstrassChordSeries.L_mul]
  simp [WeierstrassChordSeries.L_X, MvPowerSeries.constantCoeff_inv, dI_cc hw]
end Formalism.ELL.CubeTwoAlt
