-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.continuous_xiP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:13:47.230803+00:00
-- url     : https://prove2.me/submissions/619e3148-b7af-4a1e-8f63-bd145e4026bd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_cornerA
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_cornerB
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_ell
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromCols
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_fromRows
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_lowW
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_subS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_supS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cont_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_continuous_psi_comp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_cornerA
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_cornerB
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_ell
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_fromCols
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_fromRows
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_lowW
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_strictUpper
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_subS
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_supS
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.cont_upper
attribute [local fun_prop] Formalism.FourierDecayAlt.P.Ux10.continuous_psi_comp



set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : Continuous (xiP D) := by
  have key : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => ell k r z (Matrix.of M) := by
    intro z
    unfold ell
    refine continuous_finset_sum _ fun a _ => ?_
    by_cases h : a.val + 1 < r
    · simp only [h, ↓reduceDIte, Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [h, ↓reduceDIte, Matrix.mulVec, dotProduct, Matrix.of_apply]
      refine continuous_finset_sum _ fun j _ => ?_
      first
        | fun_prop
        | exact (((continuous_apply j).comp (continuous_apply (eI k r a))).mul continuous_const :)
        | continuity
  have hpsi : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => psi k r z cStd (Matrix.of M) := by
    intro z
    unfold psi
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_const.mul (key z)))))
  unfold xiP
  exact ((hpsi D.z).comp (continuous_snd.comp continuous_fst)).mul
    (continuous_star.comp ((hpsi D.z').comp (continuous_snd.comp continuous_snd)))
end Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
