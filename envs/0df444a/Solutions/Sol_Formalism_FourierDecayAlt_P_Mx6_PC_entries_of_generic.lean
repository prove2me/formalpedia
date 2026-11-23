-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.PC.entries_of_generic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:37.743692+00:00
-- url     : https://prove2.me/submissions/6b80d2dd-8d09-4e0a-b74e-44e7cb35408f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_isPoly_QQr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_bad_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.PC
open Matrix Finset Polynomial Formalism.FourierDecayAlt.M Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W
noncomputable section
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx6.PC
theorem _root_.solution
    (h : ∀ u v : ℂ, Good P u → Good P v → u - v ≠ 0 → u - v ≠ 1 → u - v ≠ -1 → ∀ i j k l : Fin 2,
      (u - v) • (QQr P u i j * QQr P v k l - QQr P v k l * QQr P u i j) =
        QQr P u k j * QQr P v i l - QQr P v k j * QQr P u i l)
    (u v : ℂ) (i j k l : Fin 2) :
    (u - v) • (QQr P u i j * QQr P v k l - QQr P v k l * QQr P u i j) =
      QQr P u k j * QQr P v i l - QQr P v k j * QQr P u i l := by
  set F : ℂ → ℂ → A P := fun u v => (u - v) • (QQr P u i j * QQr P v k l - QQr P v k l * QQr P u i j) -
    (QQr P u k j * QQr P v i l - QQr P v k j * QQr P u i l) with hF
  have hu : ∀ v, IsPoly fun u => F u v := fun v =>
    (IsPoly.smul (IsPolyS.id.sub (IsPolyS.const v))
      (((isPoly_QQr P i j).mul (IsPoly.const _)).sub ((IsPoly.const _).mul (isPoly_QQr P i j)))).sub
      (((isPoly_QQr P k j).mul (IsPoly.const _)).sub ((IsPoly.const _).mul (isPoly_QQr P i l)))
  have hv : ∀ u, IsPoly fun v => F u v := fun u =>
    (IsPoly.smul ((IsPolyS.const u).sub IsPolyS.id)
      (((IsPoly.const _).mul (isPoly_QQr P k l)).sub ((isPoly_QQr P k l).mul (IsPoly.const _)))).sub
      (((IsPoly.const _).mul (isPoly_QQr P i l)).sub ((isPoly_QQr P k j).mul (IsPoly.const _)))
  have h1 : ∀ v, Good P v → ∀ u, F u v = 0 := by
    intro v gv
    refine (hu v).eq_zero ({Y : ℂ | ¬ Good P Y} ∪ {v, v + 1, v - 1})
      ((bad_finite P).union (by simp)) ?_
    intro u hu'
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, not_not] at hu'
    obtain ⟨gu, a0, a1, a2⟩ := hu'
    exact sub_eq_zero.mpr (h u v gu gv (fun e => a0 (by linear_combination e)) (fun e => a1 (by linear_combination e))
      (fun e => a2 (by linear_combination e)) i j k l)
  have h2 : F u v = 0 := by
    refine (hv u).eq_zero {Y : ℂ | ¬ Good P Y} (bad_finite P) ?_ v
    intro v' hv'
    simp only [Set.mem_ofPred_eq, not_not] at hv'
    exact h1 v' hv' u
  exact sub_eq_zero.mp h2
end Formalism.FourierDecayAlt.P.Mx6.PC
