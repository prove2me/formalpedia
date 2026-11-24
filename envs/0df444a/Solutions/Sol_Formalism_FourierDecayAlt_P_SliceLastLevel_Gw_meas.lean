-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.Gw_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:48:10.412655+00:00
-- url     : https://prove2.me/submissions/ea932e3b-e074-4815-ab4b-1c81c9be40e3

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SliceLastLevel
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_nset_gv
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_Sn_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_mexp_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_adR_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_Gw_ck
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_exp_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_exp_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Nset_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuousOn_matrix_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuousOn_of_contDiffOn_group
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_exp_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inv_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_exp_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_rsmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_aesm_deriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
set_option linter.style.haveILetI false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {m : ℕ} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn (m : ℕ∞) (B.GV k r) F)
    (μS : Measure (Mt k r × Mt k r)) :
    ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), w.length ≤ m → ∀ P : Mt k r × Mt k r → B.Mat k r,
      ContinuousOn P (Sn k r) → (∀ ξ ∈ Sn k r, P ξ ∈ B.GV k r) →
      AEStronglyMeasurable (fun ξ => Set.indicator (Sn k r) (fun ξ => Gw F ξ w (P ξ)) ξ) μS := by
  intro w
  induction w with
  | nil =>
    intro _ P hP hPG
    have hc : ContinuousOn (fun ξ => Gw F ξ [] (P ξ)) (Sn k r) :=
      (Formalism.FourierDecayAlt.P.B6.continuousOn_of_contDiffOn_group hF).comp hP hPG
    exact (aestronglyMeasurable_indicator_iff Sn_closed.measurableSet).2
      (hc.aestronglyMeasurable Sn_closed.measurableSet)
  | cons i w ih =>
    intro hl P hP hPG
    have hl' : w.length + 1 ≤ m := by simpa using hl
    set X : Mt k r × Mt k r → B.Mat k r := fun ξ => adR (Matrix.of ξ.2) i with hXdef
    have hX : ContinuousOn X (Sn k r) :=
      Formalism.FourierDecayAlt.P.B6.continuousOn_matrix_mul (Formalism.FourierDecayAlt.P.B6.continuousOn_matrix_mul
        ((Formalism.FourierDecayAlt.P.B6.inv_continuousOn k r).comp continuous_snd.continuousOn
          (fun ξ h => Formalism.FourierDecayAlt.P.B6.Nset_sub _ _ h.2)) continuousOn_const) continuous_snd.continuousOn
    have hd : ∀ ξ, HasDerivAt
        (fun t : ℝ => Set.indicator (Sn k r)
          (fun ξ => Gw F ξ w (P ξ * NormedSpace.exp ((t : ℂ) • X ξ))) ξ)
        (Set.indicator (Sn k r) (fun ξ => Gw F ξ (i :: w) (P ξ)) ξ) 0 := by
      intro ξ
      by_cases hξ : ξ ∈ Sn k r
      · simp only [Set.indicator_of_mem hξ]
        have hn' : (Matrix.of ξ.2 : B.Mat k r) ∈ B.GV k r := nset_gv hξ.2
        have hck : B.CkOn (((0 : ℕ) + 1 : ℕ) : ℕ∞) (B.GV k r) (Gw F ξ w) := by
          have := Gw_ck hF hn' w (by omega)
          exact Formalism.FourierDecayAlt.P.B4.ckOn_mono (by omega) this
        have hdiff := Formalism.FourierDecayAlt.P.B4.ckOn_diff 0 false hck (adR_lie hn' i) (hPG ξ hξ)
        exact hdiff.hasDerivAt
      · simp only [Set.indicator_of_notMem hξ]
        exact hasDerivAt_const _ _
    refine Formalism.FourierDecayAlt.P.Ux10.aesm_deriv hd (Eventually.of_forall fun t => ?_)
    refine ih (by omega) (fun ξ => P ξ * NormedSpace.exp ((t : ℂ) • X ξ)) ?_ ?_
    · exact Formalism.FourierDecayAlt.P.B6.continuousOn_matrix_mul hP
        ((mexp_cont _).comp_continuousOn (hX.const_smul ((t : ℂ))))
    · intro ξ hξ
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (hPG ξ hξ)
        (Formalism.FourierDecayAlt.P.BetaSesquilinearity.exp_mem (Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_rsmul (adR_lie (nset_gv hξ.2) i) t))
end Formalism.FourierDecayAlt.P.SliceLastLevel
