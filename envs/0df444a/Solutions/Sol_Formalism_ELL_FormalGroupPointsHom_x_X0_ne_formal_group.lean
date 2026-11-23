-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsHom.x_X0_ne_formal_group
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:17.502279+00:00
-- url     : https://prove2.me/submissions/9d9b52b8-cfec-4bee-9026-8a9af30663ad

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_hasSubst2
import Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_fg_ne_zero
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_exists_unit_factor
import Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_xOf_ne_of_hom
import Theorems.Thm_P2M_Formalism_ELL_WeierstrassCoordinateSubstitution_X_ne_zero__047225846678


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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [Field K]
namespace Formalism.ELL.FormalGroupPointsHom
theorem _root_.solution {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w)
    (F : FormalGroup K) :
    xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ xOf w F.toPowerSeries := by
  obtain ⟨u0, hwu, hu⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  have hφ : MvPowerSeries.HasSubst
      ![(0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] := hasSubst2 (by simp) (by simp)
  refine WeierstrassCoordinateSubstitution.xOf_ne_of_hom hwu hu (MvPowerSeries.substAlgHom hφ) _ _ (by simp)
    F.zero_constantCoeff (WeierstrassCoordinateSubstitution.X_ne_zero' 0) (fg_ne_zero F) ?_ ?_
  · rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hφ]; rfl
  · rw [MvPowerSeries.coe_substAlgHom,
      F.zero_add (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
    exact WeierstrassCoordinateSubstitution.X_ne_zero' 1
end Formalism.ELL.FormalGroupPointsHom
