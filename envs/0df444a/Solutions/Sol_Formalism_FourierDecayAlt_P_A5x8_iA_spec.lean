-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.iA_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:52.47339+00:00
-- url     : https://prove2.me/submissions/b197c7da-5e43-4bbb-9b89-d15dd1d13213

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_iso_dot_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_mk_outV
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K) {m : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (Z : Matrix (Fin m) (Fin m) K) (α : coker R Z →ₗ[R] KR R) (v : Fin m → R) :
    α (Submodule.Quotient.mk v) = Submodule.Quotient.mk (outV R (iA R Z α) ⬝ᵥ coeLin R v) := by
  have key : α.comp (Submodule.mkQ _) =
      (Submodule.mkQ _).comp (iso_dot R (outV R (iA R Z α))) := by
    ext j
    have hc : coeLin R (Pi.single j (1 : R)) = Pi.single j (1 : K) := by
      funext k
      by_cases hk : k = j
      · subst hk
        simp [coeLin]
      · simp [coeLin, Pi.single_apply, hk]
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, iso_dot_apply, LinearMap.single_apply]
    rw [hc, dotProduct_single, mul_one, mk_outV]
    rfl
  have h := LinearMap.congr_fun key v
  simpa [iso_dot_apply] using h
end Formalism.FourierDecayAlt.P.A5x8
