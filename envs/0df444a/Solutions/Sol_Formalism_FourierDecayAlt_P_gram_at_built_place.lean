-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gram_at_built_place
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:22:01.314775+00:00
-- url     : https://prove2.me/submissions/9eee8f15-5388-4d44-bf2e-5918f029fbe3

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_vecV_cutF_eventually
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_vecV_of_not
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_hsVec_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JC.GramPlaceBuilt := by
  intro _ hGS _ _ _ E _ _ _ Wp Wq _ _ _ _ _ S T f χ ν' m₀ top A₀ _ _ hB v Y hY
  obtain ⟨hχ, hv⟩ := hB
  have hpd := (hv v).1
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ p ∈ Y,
      D.vecV (T v).base (ν' v) (m₀ v) (D.cutF (T v).base χ (f v) ε) (D.toStd S.G.r (S.g : ℝ) 1 p) =
        D.vecV (T v).base (ν' v) (m₀ v) (f v) (D.toStd S.G.r (S.g : ℝ) 1 p) := by
    rw [Filter.eventually_all_finset]
    intro p _
    exact Formalism.FourierDecayAlt.P.JCx1.needs.vecV_cutF_eventually hGS _ _ _ χ hχ _ _
  filter_upwards [hev] with ε hε
  intro p hp q hq
  rw [hpd]
  simp only [D.componentFamilySetting_ofSetting, D.RRplace, JC.vecPlace]
  by_cases hpq : D.IsLocPt (D.toStd S.G.r (S.g : ℝ) 1 p) (S.G.r + 1) ∧
      D.IsLocPt (D.toStd S.G.r (S.g : ℝ) 1 q) (S.G.r + 1)
  · simp only [dif_pos hpq, dif_neg (show ¬ (S.G.r + 1 ≤ S.G.r) by omega), ↓reduceIte]
    rw [hε p hp, hε q hq]
    simp only [D.GamLev, Finset.Ioc_self, Finset.prod_empty, one_pow, hsInner, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal]
    push_cast
    ring
  · rw [dif_neg hpq]
    rcases not_and_or.mp hpq with h | h
    · rw [Formalism.FourierDecayAlt.P.JCx1.needs.vecV_of_not h]
      simp [Formalism.FourierDecayAlt.P.JCx1.needs.hsVec_zero]
    · rw [Formalism.FourierDecayAlt.P.JCx1.needs.vecV_of_not h]
      simp [Formalism.FourierDecayAlt.P.JCx1.needs.hsVec_zero]
end Formalism.FourierDecayAlt.P
