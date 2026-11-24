-- Prove2me | solution 1 for Formalism.L2.DIV.det_in_unitary_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:44:18.826649+00:00
-- url     : https://prove2.me/submissions/67925736-0301-428a-a593-cb5e914f55c2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_unitary_det_norm_one
import Theorems.Thm_Formalism_L2_DIV_conjugation_units_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
namespace Formalism.L2.DIV
theorem _root_.solution : DetInUnitaryOne := by
  intro F E _ _ _ _ _ σ n J hJ g hg
  have hJ' : IsUnit (J.map (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F))).det := by
    have : (J.map (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F))).det =
        inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) J.det := by
      rw [RingHom.map_det]; rfl
    rw [this]; exact hJ.map _
  have h := unitary_det_norm_one _ _ hJ' g hg
  rw [U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply]
  apply Units.ext
  rw [Units.val_mul, conjugation_units_val, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, mul_comm]
  exact h
end Formalism.L2.DIV
